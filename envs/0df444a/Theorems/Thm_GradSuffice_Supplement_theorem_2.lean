-- Prove2me | Theorems.Thm_GradSuffice_Supplement_theorem_2
-- name    : GradSuffice.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:28:46.061969+00:00
-- url     : https://prove2.me/theorems/c9014b9a-4776-4938-865f-eda7310181aa
-- title:
--   Theorem 2, p.9 — $\mathcal R^{(s)}_m(B)>e\,m^{-1/q}$ forces $T_A(\varepsilon)>\exp(cq)\log(1/\varepsilon)$
-- statement:
--   There are universal constants $q_0\ge2$, $c>0$ and $\varepsilon_0\in(0,1)$ with the following property. Let $B$ be the unit ball of a real Banach space $X$ and fix $q\ge q_0$. If
--   $$\mathcal R^{(s)}_m(B)>e\,m^{-1/q}\qquad\text{for some integer } m\ge1,$$
--   then for every $0<\varepsilon<\varepsilon_0$, every $\varepsilon$-accurate first-order optimization algorithm $A$, possibly randomized, has iteration complexity
--   $$T_A(\varepsilon)>\exp(cq)\,\log(1/\varepsilon).$$
--   Here an $\varepsilon$-accurate algorithm makes $T$ queries and, for every convex 1-Lipschitz objective and every valid oracle, returns a point $w_T$ with $\Pr[f(w_T)-\inf_B f\le\varepsilon]\ge1/2$ over its internal randomness.
--
--   A single scale $m$ at which the sequential Rademacher complexity is large forces a number of queries exponential in $q$; it is the lower-bound counterpart of item (iii) of the §2 Theorem.
--
--   **Formalization Note** A randomized algorithm is a family of deterministic $T$-query algorithms indexed by a probability space, and accuracy is the published `GradSuffice.IsAccurate`. The logarithm is natural.
--
--   Differences from the source:
--   - encoding: R⁽ˢ⁾ₘ(B) > e m^{−1/q} (a supremum over adaptive sequences) → some B⋆-valued adaptive sequence ξ of length m has seqRad ξ > e m^{−1/q}; reason: a supremum exceeds a number iff some element does
--   - encoding: universal constants q₀ ≥ 2, c > 0, ε₀ ∈ (0, 1) → ∃ q₀ ≥ 2, c > 0, 0 < ε₀ < 1 chosen before the space X, q and m; reason: quantifier form of "universal"
--   - encoding: an algorithm making at most T_A(ε) queries → an algorithm making exactly T queries, 0 < T (A : Ω → DetAlg X B T), and the bound exp(cq) log(1/ε) < T; reason: an algorithm with fewer queries is padded by repeating its last query (base DetAlg / IsAccurate convention); the output is the last query, so T ≥ 1
--   - encoding: a (real Banach) space X, with no restriction on its size → X : Type (the lowest universe); reason: the constants are quantified before X, so X ranges over one fixed universe; universe-level convention, as in the base mission's theorem_sec2_i and theorem_3
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 2, p.9

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_seqRad
import Definitions.Def_GradSuffice_IsAccurate

namespace GradSuffice.Supplement

/-- **Theorem 2 (lower bound from sequential Rademacher complexity).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 2, p.9: "There
exist universal constants `q₀ ≥ 2`, `c > 0`, and `ε₀ ∈ (0, 1)` such that the following holds. Let `B`
be the unit ball of a real Banach space, and fix `q ≥ q₀`. If `R⁽ˢ⁾ₘ(B) > e m^{−1/q}` for some integer
`m ≥ 1`, then, for every `0 < ε < ε₀`, every ε-accurate first-order optimization algorithm `A`,
possibly randomized, has iteration complexity `T_A(ε) > exp(cq) log(1/ε)`."

**Formalization Note.** `q₀, c, ε₀` are chosen before the space. `R⁽ˢ⁾ₘ(B) > e m^{−1/q}` is "some
`B⋆`-valued adaptive sequence of length `m` has `R⁽ˢ⁾ₘ(B; ξ) > e m^{−1/q}`" (as in the base
Theorem 3). A randomized algorithm with `T` queries is a family `A : Ω → DetAlg X B T` over a
probability space, and ε-accuracy is the base `IsAccurate` (every convex 1-Lipschitz objective,
every valid oracle, success probability `≥ 1/2`); an algorithm with fewer queries is padded, so the
query bound is `T` itself (`0 < T`, the output being the last query). `log` is natural. -/
theorem theorem_2 :
    ∃ q₀ : ℝ, 2 ≤ q₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (q : ℝ), q₀ ≤ q →
      ∀ m : ℕ, 1 ≤ m →
        (∃ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ ∧
          Real.exp 1 * (m : ℝ) ^ (-1 / q) < seqRad ξ) →
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∀ T : ℕ, 0 < T → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure μ] (A : Ω → DetAlg X (Metric.closedBall (0 : X) 1) T),
          IsAccurate (Metric.closedBall (0 : X) 1) ε μ A →
          Real.exp (c * q) * Real.log (1 / ε) < T := by sorry

end GradSuffice.Supplement
