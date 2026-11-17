-- Prove2me | Theorems.Thm_MatMulTimeLP_Supplement_theorem_5_12
-- name    : MatMulTimeLP.Supplement.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:57:45.937485+00:00
-- url     : https://prove2.me/theorems/6f1d250c-ee88-4ce0-bc15-3cfc10adaeb9
-- title:
--   Theorem 5.12 — adaptive exact residual sampler with uniform operation bounds
-- statement:
--   There are absolute positive constants $C_{\rm init}$, $C_{\rm upd}$ and $C_{\rm samp}$ and a constant $C_{\rm ops}\ge 1$ such that the following holds for every $n\ge1$. For every fixed matrix $H\in\mathbb R^{n\times n}$ and vector $h\in\mathbb R^n$, a randomized exact-real-RAM data structure maintains $z\in\mathbb R^n$, initially $0$, and writes
--
--   $$
--   r=Hf(z)+h-z,\qquad f(t)=\sqrt{t^2+4}-2.
--   $$
--
--   An update replaces one coordinate $z_i$ in at most $C_{\rm upd}\log^3(2+n)$ instructions. For every sample call with $U\ge4\|r\|_2^2$, the ideal conditional answer law is
--
--   $$
--   \Pr[I=i\mid\text{previous history}]=\frac{r_i^2}{U},
--   \qquad
--   \Pr[I=\bot\mid\text{previous history}]=1-\frac{\|r\|_2^2}{U}.
--   $$
--
--   Against every adaptive adversary that sees previous answers but not internal state or randomness and issues at most $C_{\rm ops}n^3$ interleaved calls, the implementation transcript can be coupled to this ideal transcript with disagreement probability at most $n^{-10}$. Initialization costs at most $C_{\rm init}n^2\log^4(2+n)$ instructions. Along every such adaptive run, the expected total sampling work is at most the sum, over its sample calls, of
--
--   $$
--   C_{\rm samp}\left(\log^4(2+n)+n\log^4(2+n)\frac{\|r\|_2^2}{U}\right),
--   $$
--
--   so the additive overhead from footnote 4 remains present even when $r=0$. Every call is a first-halting execution of the persistent real-RAM programs, and sampling preserves $z$.
--
--   This theorem supplies the exact adaptive sampler used by the paper’s fast implementation, rather than merely the fixed-residual accuracy and one-query laws of Lemmas A.2 and A.3.
--
--   **Formalization Note** Coordinates are 0-based `Fin n`; `Fail` is distinct from the no-sample answer $\bot$. The high-probability statement is a literal coupling with the published ideal transcript probability, and the expected-work inequality sums the per-history call budgets.
--
--   Differences from the source:
--   - encoding: coordinates $\{1,\ldots,n\}$, answers $\{1,\ldots,n\}\cup\{\bot\}$ and an implicit low-probability failure → `Fin n`, `Answer.coord`, `Answer.bot` and `Answer.fail`; reason: zero-based indexing and an explicit failure outcome preserve every source case
--   - encoding: a stateful randomized data structure and its charged operations → three persistent programs of the published exact-real RAM, fixed call-memory layouts, first-halt times and independent call tapes; reason: this makes the paper’s machine-step costs operational and prevents loaders or free cost fields from doing the work
--   - reading: exact conditional probabilities and correctness at least $1-n^{-10}$ against an adaptive adversary → for every valid adaptive adversary, a coupling of the implementation transcript with the published ideal sampler whose mismatch mass is at most $n^{-10}$; reason: equality with the ideal transcript on the coupled success event is precisely simultaneous conditional correctness for every call
--   - encoding: $O(\log^3 n)$, $O(n^2\log^4 n)$, $O(n^3)$ and footnote 4’s $O(\log^4 n+n\log^4 n\,\|r\|_2^2/U)$ → positive universal constants before all instances, operation histories and adversaries, with $\log(2+n)$ and an accumulated expected-work inequality; reason: standard uniform finite-size reading of the asymptotic bounds, retaining both query terms and changing no asymptotic instance
--   - generalization: for each fixed $H,h$ there is a data structure → for each dimension one program triple works for every $H,h$ supplied in input memory; reason: Algorithm 6 is uniform in the entries of $H,h$, and specializing the uniform implementation gives the source statement
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…), Theorem 5.12, p.32; proof Appendix A, pp.44–48; query-time footnote 4, p.32

import Mathlib
import Definitions.Def_MatMulTimeLP_Supplement_ResidualSamplerImplementation

namespace MatMulTimeLP

namespace Supplement

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 5.12, p.32 and Appendix A,
pp.44–48: for every fixed `H` and `h`, a randomized data structure maintains `z`, initially zero;
updates cost `O(log^3 n)`; and `Sample(U)`, for `U ≥ 4‖Hf(z)+h-z‖₂²`, returns coordinate `i`
with conditional probability `r_i²/U` and `⊥` with the remaining probability.  Up to `O(n³)`
adaptive calls are simultaneously correct with probability at least `1-n⁻¹⁰`; initialization costs
`O(n² log^4 n)` and a sample costs expected
`O(log^4 n + n log^4 n · ‖r‖₂²/U)`, including footnote 4.

**Formalization Note** Coordinates are `Fin n` (0-based).  A single program triple works for all
`H,h` of a fixed size.  Correctness against every adaptive caller is a coupling of the exact
real-RAM transcript with the published ideal sampler; mismatch probability is at most `n⁻¹⁰`.
The work inequality sums the conditional per-query bounds along an adaptive run, which is
equivalent to the paper's expected per-call accounting.  `log(2+n)` states the asymptotic
`log n` costs uniformly at the finitely many small sizes without imposing a size threshold. -/
theorem theorem_5_12 :
    ∃ (Cinit Cupdate Csample Cops : ℝ),
      0 < Cinit ∧ 0 < Cupdate ∧ 0 < Csample ∧ 1 ≤ Cops ∧
      ∀ n : ℕ, 1 ≤ n → ∃ I : ResidualSamplerImplementation n,
        ∀ (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ),
          -- initialization: first halt, zero maintained vector, and uniform work
          (∀ ω,
            HaltsFromAt I.initProgram ω (residualInitState H h) (I.initTime H h ω) ∧
            residualStateZ (n := n) (I.initResult H h ω) = (0 : Fin n → ℝ) ∧
            ((I.initTime H h ω + 1 : ℕ) : ℝ) ≤
              Cinit * (n : ℝ) ^ 2 * dsLog n ^ 4) ∧
          -- every reachable update preserves the persistent representation and changes only z_i
          (∀ (s : State), I.Reachable H h s → ∀ (i : Fin n) (zi : ℝ) (ω : Tape),
            HaltsFromAt I.updateProgram ω (loadResidualUpdate s i zi) (I.updateTime s i zi ω) ∧
            residualStateZ (n := n) (I.updateResult s i zi ω) =
              Function.update (residualStateZ (n := n) s) i zi ∧
            ((I.updateTime s i zi ω + 1 : ℕ) : ℝ) ≤ Cupdate * dsLog n ^ 3) ∧
          -- sampling does not alter z and has the deterministic worst-case walk bound
          (∀ (s : State), I.Reachable H h s → ∀ (U : ℝ) (ω : Tape),
            HaltsFromAt I.sampleProgram ω (loadResidualSample (n := n) s U) (I.sampleTime s U ω) ∧
            residualStateZ (n := n) (I.sampleResult s U ω) = residualStateZ (n := n) s ∧
            ((I.sampleTime s U ω + 1 : ℕ) : ℝ) ≤ Csample * n * dsLog n ^ 4) ∧
          -- adaptive exactness, operation cap, and expected query cost (including the additive term)
          ∀ (adv : Adversary n) (m : ℕ),
            (m : ℝ) ≤ Cops * (n : ℝ) ^ 3 → ValidAdv H h adv m 0 [] →
            Measurable (fun Ω : CallTapes =>
              ((residualRun I H h adv m Ω).sampleWork : ℝ≥0∞)) ∧
            Measurable (fun Ω : CallTapes =>
              ENNReal.ofReal (Csample * (residualRun I H h adv m Ω).sampleScale)) ∧
            (∀ Ω,
              ((residualRun I H h adv m Ω).updateWork : ℝ) ≤
                Cupdate * (residualRun I H h adv m Ω).updateCount * dsLog n ^ 3) ∧
            (∫⁻ Ω, ((residualRun I H h adv m Ω).sampleWork : ℝ≥0∞) ∂callTapesLaw) ≤
              ∫⁻ Ω, ENNReal.ofReal (Csample * (residualRun I H h adv m Ω).sampleScale)
                ∂callTapesLaw ∧
            ∃ c : PMF (Transcript n × Transcript n),
              (∀ t, (c.map Prod.fst) t =
                callTapesLaw {Ω | (residualRun I H h adv m Ω).transcript = t}) ∧
              (∀ t, (c.map Prod.snd) t = ENNReal.ofReal (idealProb H h adv m 0 [] t)) ∧
              c.toOuterMeasure {p | p.1 ≠ p.2} ≤
                ENNReal.ofReal (1 / (n : ℝ) ^ 10) := by sorry

end Supplement

end MatMulTimeLP
