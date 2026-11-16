-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_1_11
-- name    : GaussPart.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:12:30.442033+00:00
-- url     : https://prove2.me/theorems/a399847c-1887-41ff-a3e3-f0514787a358
-- title:
--   Theorem 1.11 (Lemma 6.3) — from PUI to reliable learning (corrected: work bound $C(T/\epsilon+(d+1)/\epsilon^2)$ in the sampling-RAM cost model)
-- statement:
--   This is Theorem 1.11 at the precision of its formal version, Lemma 6.3.
--
--   **Setting.** Let $\mathcal F$ be a class of functions on $\mathbb R^d$ and let $A$ be a PUI learner for $\mathcal F$ with reference $\mathcal N(0,I_d)$, sample complexity $N(\epsilon,\sigma,p_+,q)$, running time $T(\epsilon,\sigma,p_+,q)$ and failure probability at most $1/12$, where $p_+>0$ is a given lower bound on the probability that the target equals $1$. Let $D$ be a distribution on $\mathbb R^d\times\{\pm1\}$ whose x-marginal is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$, $q\ge1$, $\sigma\in(0,1]$, $\epsilon\in(0,1/2)$.
--
--   **Theorem.** There is a universal constant $C$ such that:
--
--   1. if $\mathcal F$ contains the constant $1$, there is an algorithm that negatively reliably learns $\mathcal F$ under $D$ with probability at least $2/3$, using at most
--   $$
--   C\Bigl(\frac{N(\epsilon/2,\sigma\epsilon/4,\epsilon/4,q)}{\epsilon}+\frac1{\epsilon^2}\Bigr)
--   $$
--   labeled samples and work at most $C\bigl(T(\epsilon/2,\sigma\epsilon/4,\epsilon/4,q)/\epsilon+(d+1)/\epsilon^2\bigr)$;
--   2. if $\mathcal F$ contains the constant $-1$ and $-\mathcal F$ admits such a PUI learner, then $\mathcal F$ is positively reliably learnable under $D$ with the same bounds.
--
--   The reduction feeds the PUI learner the examples with label $1$ (rejection sampling); combined with Theorem 5.3 it gives Theorem 6.2.
--
--   **Formalization Note** The reliable learner is built from $A$ and is given $\epsilon,\sigma,q$ and the two numbers $N(\epsilon/2,\sigma\epsilon/4,\epsilon/4,q)$, $T(\epsilon/2,\sigma\epsilon/4,\epsilon/4,q)$. In the published machine reading a labeled sample costs $d+1$, which is where the term $(d+1)/\epsilon^2$ comes from.
--
--   Differences from the source:
--   - correction: time O(T(ϵ/2, σϵ/4, ϵ/4, q)/ϵ + 1/ϵ²) → work ≤ C(T(ϵ/2, σϵ/4, ϵ/4, q)/ϵ + (d + 1)/ϵ²); reason: in the sampling-RAM cost model (a labeled sample costs d + 1) the printed bound is false: for F = {1, −1} the program outputting the constant 1 is a PUI learner with N ≡ 0 and constant T, while any negative reliable learner must read a sample (all-positive and all-negative labels need different answers), costing d + 1, unbounded in d
--   - encoding: the reliable learner uses N(·) and T(·) and enforces A's limits → the learner, built from A after N, T and A, is given ϵ, σ, q and the numbers N(ϵ/2, σϵ/4, ϵ/4, q), T(ϵ/2, σϵ/4, ϵ/4, q); reason: a finite program cannot evaluate arbitrary real functions N and T
--   - encoding: a PUI learner A with sample complexity N, running time T and failure probability at most 1/12 → IsPUILearner F N T A E_A: for every ϵ ∈ (0,1), σ ∈ (0,1], p₊ ∈ (0,1], q ≥ 1, at most N samples and work T on every stream, hypotheses evaluated within T, success ≥ 11/12 on samples of D∗₊ only; reason: Definitions 1.7 and 5.1 on the machine
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: O(·), poly(·) (both O(·) of Lemma 6.3) → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 1.11, p.6 (PDF p.8); formal version Lemma 6.3, p.61 (PDF p.63)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_PUILearner

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 1.11** (From PUI to Reliable Learning), stated at the precision of its formal version
**Lemma 6.3** (Reduction from Reliable Learning to Smoothed PUI Learning).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 1.11, p.6 (PDF p.8);
Lemma 6.3, p.61 (PDF p.63).

Lemma 6.3: "Let G = N(0, I_d), let D be a distribution over ℝ^d × {±1} whose x-marginal is
(q, σ)-smooth with respect to G, where q ≥ 1 and σ ∈ (0, 1], and let ϵ ∈ (0, 1/2). Assume that F
contains the constant function 1 and admits a PUI learner A with failure probability at most 1/12,
sample complexity N(ϵ, σ, p+, q), and running time T(ϵ, σ, p+, q), where p+ > 0 is a given lower
bound on the probability that the target function equals 1. Then there exists an algorithm that
negatively reliably learns F under D with probability at least 2/3, using
O(N(ϵ/2, σϵ/4, ϵ/4, q)/ϵ + 1/ϵ²) labeled samples and O(T(ϵ/2, σϵ/4, ϵ/4, q)/ϵ + 1/ϵ²) time.
Consequently, if F contains the constant function −1 and −F admits such a PUI learner, then F is
positively reliably learnable under D, with the same complexity bounds for the learner of −F."

**Formalization Note.**
* One universal constant `C` serves both `O(·)`; it is chosen before `d`, `F`, `N`, `T` and the
  learner `A`. `A` (with its evaluator `EA`) is a PUI learner in the sense of `IsPUILearner`: sample
  count `N(·)` and work `T(·)` on every stream, hypotheses evaluated within work `T(·)`, success
  `≥ 11/12`, fed samples of `D∗₊` only. The reliable learner `B` is built from `A`; it receives
  `ϵ, σ, q` and the two numbers `N(ϵ/2, σϵ/4, ϵ/4, q)`, `T(ϵ/2, σϵ/4, ϵ/4, q)` (a finite program cannot
  evaluate arbitrary functions `N, T`; the page's proof uses `n = ⌈N(…)⌉` and enforces `A`'s limits).
* **Correction of the time bound.** The published machine charges `d + 1` for reading one labeled
  sample, so the work bound is `C(T(…)/ϵ + (d + 1)/ϵ²)`: the printed `O(T/ϵ + 1/ϵ²)` fails in this
  cost model. Counterexample: `F = {1, −1}`; the program that outputs the constant `1` is a PUI learner
  for `F` (a target with `D∗(f = 1) > 0` is the constant `1`) with `N ≡ 0` and constant `T`; any
  negative reliable learner must read a sample (labels all `1` and all `−1` need different answers),
  which costs `d + 1`, unbounded in `d`.
* Both parts: the negative clause for `F ∋ 1` and the positive clause for `F ∋ −1` whose class
  `−F = negClass F` has a PUI learner. Labeled samples, bounds on every stream, success on a measurable
  set, evaluated hypotheses: as in `theorem_4_2`. `d ≥ 1`. -/
theorem theorem_1_11 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (F : Set (Vec d → ℝ)) (N T : ℝ → ℝ → ℝ → ℝ → ℝ)
      (A EA : GaussMixHH.Program), GaussMixHH.Admissible A → ArithmeticOnly A →
      GaussMixHH.Admissible EA → ArithmeticOnly EA →
    ((fun _ => (1 : ℝ)) ∈ F → IsPUILearner F N T A EA →
      ∃ (B : GaussMixHH.Program) (_ : GaussMixHH.Admissible B) (_ : ArithmeticOnly B)
        (EB : GaussMixHH.Program) (_ : GaussMixHH.Admissible EB) (_ : ArithmeticOnly EB),
      ∀ (q σ ε : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < ε → ε < 1 / 2 →
        let nA : ℝ := N (ε / 2) (σ * ε / 4) (ε / 4) q
        let tA : ℝ := T (ε / 2) (σ * ε / 4) (ε / 4) q
        let inp : List ℝ := [ε, σ, q, nA, tA]
        RunsWithin B (d + 1) inp (C * (nA / ε + 1 / ε ^ 2)) (C * (tA / ε + (d + 1) / ε ^ 2)) ∧
        ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
          IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
          SucceedsWith B (d + 1) inp (labeledStream D) (2 / 3)
            (fun s => NegReliable F D ε (hyp EB d (C * (tA / ε + (d + 1) / ε ^ 2)) s))) ∧
    ((fun _ => (-1 : ℝ)) ∈ F → IsPUILearner (negClass F) N T A EA →
      ∃ (B : GaussMixHH.Program) (_ : GaussMixHH.Admissible B) (_ : ArithmeticOnly B)
        (EB : GaussMixHH.Program) (_ : GaussMixHH.Admissible EB) (_ : ArithmeticOnly EB),
      ∀ (q σ ε : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < ε → ε < 1 / 2 →
        let nA : ℝ := N (ε / 2) (σ * ε / 4) (ε / 4) q
        let tA : ℝ := T (ε / 2) (σ * ε / 4) (ε / 4) q
        let inp : List ℝ := [ε, σ, q, nA, tA]
        RunsWithin B (d + 1) inp (C * (nA / ε + 1 / ε ^ 2)) (C * (tA / ε + (d + 1) / ε ^ 2)) ∧
        ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
          IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
          SucceedsWith B (d + 1) inp (labeledStream D) (2 / 3)
            (fun s => PosReliable F D ε (hyp EB d (C * (tA / ε + (d + 1) / ε ^ 2)) s))) := by sorry

end Supplement

end GaussPart
