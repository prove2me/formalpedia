-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_theorem_1_2
-- name    : MaoLowDegree.Counterexample.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:35.858206+00:00
-- url     : https://prove2.me/theorems/6722c451-b8a0-48a0-a237-13affed7618c
-- title:
--   Theorem 1.2 — the polynomial-time low-degree conjecture is false
-- statement:
--   For every fixed integer $r\ge3$, there are constants $c_r>0$, $0<\varepsilon_r<1$, a sequence of permutation-invariant graph laws $P_n$, and one deterministic finite program $A$, such that, for
--   $$D_n=\lfloor c_r(\log_2n)^{r-1}\rfloor,$$
--   all sufficiently large $n$ have exactly uniform marginals on every set of at most $D_n$ edges, and $\operatorname{Adv}_{\le D_n}(P_n,Q_n)=0$. The program $A$ runs in $O(n^2)$ time and, for every fixed $\varepsilon\in[0,\varepsilon_r]$, satisfies both limits
--   $$\Pr_{Y\sim T_\varepsilon P_n}[A(Y)=\mathrm{Planted}]\longrightarrow1,\qquad \Pr_{Y\sim Q_n}[A(Y)=\mathrm{Null}]\longrightarrow1.$$
--
--   The same $A$ is fixed before $\varepsilon$, receives neither the noise rate nor advice, and works for every $n$. Moreover, one randomized finite program, given unary $n$ and advice $a_n$ fixed independently of its fresh coins, samples exactly from $P_n$ for every $n$, with
--   $$|a_n|=O\bigl(n\log_2n+(\log_2n)^{2r}\bigr),\qquad \mathbb E\tau_n\le C(n+1)^p.$$
--   The programs and all constants may depend on $r$, but are fixed before $n$. The advice asymptotic bound has its constant fixed before $n$; sampling time is the actual untruncated expected stopping time.
--
--   Finally, the universal Conjecture 1.1 is false, including its quantification over randomized polynomial-time tests and arbitrary permutation-invariant graph laws. No supporting bias, puncturing, marginal, rank, runtime, or sampler result is a premise of this theorem. The four unnumbered obligations—symmetry, degree comparison, execution time, and advice sampling—remain in this goal.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and unordered edges → Fin n with increasing endpoint pairs; n=0 is an empty-cube extension; reason: relabeling by subtracting one changes no positive-n instance
--   - encoding: for all sufficiently large n and probability 1-o(1) → Filter.atTop eventual assertions and Tendsto to 1; reason: these are the literal asymptotic quantifiers, with all fixed parameters before n
--   - encoding: real L²(Q) orthogonal projection → finite Walsh expansion and referenced finite L² sum; reason: the uniform null has full support and Walsh characters span the same real degree space
--   - reading: unnamed computation model counting F₂ operations and input access → fixed finite bit-RAM with bounded address counters, bit memory and step-counted operational execution; reason: Algorithm 1 and pp.14–15 support random access; logarithmic addressing overhead in the subquadratic work is absorbed by the strict exponent slack
--   - encoding: randomized exact sampler in expected polynomial time → unconditional first-halting cylinder output masses and extended tail-sum expected stopping time; reason: represents an infinite fair coin stream and gives nontermination infinite time without truncation or conditioning
--   - encoding: asymptotic degree lower bound and bounded advantage in Conjecture 1.1 → eventual degree comparison and eventual bound for arbitrary graph-law families; reason: finite prefixes can be adjusted without changing strong distinction or bounded finite-cube advantage
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Theorem 1.2, p.5; Conjecture 1.1, p.4; completion, pp.14–15

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Theorem 1.2 (Conjecture 1.1 is false), p.5, including the exact sampler.
No bias, puncturing, marginal, rank, or runtime theorem is assumed. -/
theorem theorem_1_2 :
    (∀ r : ℕ, 3 ≤ r →
      ∃ c εᵣ : ℝ, 0 < c ∧ 0 < εᵣ ∧ εᵣ < 1 ∧
      ∃ P : GraphFamily, ∃ A : BitProgram,
        (∀ n : ℕ, PermutationInvariant (P n)) ∧
        (∀ᶠ n : ℕ in atTop,
          MarginalUniform (P n) (degreeThreshold r c n) ∧
          advantage (P n) (degreeThreshold r c n) = 0) ∧
        QuadraticTest A ∧
        (∀ ε : Rate, ε.val ≤ εᵣ → StronglyDistinguishes A (fun n => noise ε (P n))) ∧
        ExactAdviceSampler r P) ∧
      ¬ PolynomialTimeLowDegreeConjecture := by sorry

end MaoLowDegree.Counterexample
