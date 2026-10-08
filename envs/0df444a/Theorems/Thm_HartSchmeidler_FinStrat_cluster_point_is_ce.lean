-- Prove2me | Theorems.Thm_HartSchmeidler_FinStrat_cluster_point_is_ce
-- name    : HartSchmeidler.FinStrat.cluster_point_is_ce
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:09:22.483986+00:00
-- url     : https://prove2.me/theorems/42f07fb4-9cd4-4f9c-a90f-f2d2e1cbd5fa
-- title:
--   Proof of Theorem 2(ii) — the cluster point satisfies condition (3)
-- statement:
--   Let each $S^i$ be nonempty, finite, and discrete, and let each payoff $h^i$ be continuous on $S=\prod_i S^i$. Fix a profile $\hat s$. For every f-set $T$ containing $\hat s$, choose a finite weighted correlated equilibrium $(F_T,w_T)$ of $\Gamma_T$. Suppose the probability measure $p$ on the product σ-algebra is a weak cluster point of this family: for every continuous $f:S\to\mathbb R$, every $\varepsilon>0$, and every anchored f-set $T_0$, some anchored $T\supseteq T_0$ satisfies
--
--   $$\left|\int f,dp-\sum_{s\in F_T}w_T(s)f(s)\right|<\varepsilon.$$
--
--   Then $p$ is a countably additive correlated equilibrium: for every player $i$ and $r^i,t^i\in S^i$, the integral in condition (3) exists and is nonnegative.
--
--   **Formalization Note.** The test function is zero off the cylinder $\{s:s^i=r^i\}$ and equals $h^i(s)-h^i(s^{-i},t^i)$ on it; continuity follows from discrete $S^i$. Anchoring repairs the paper's nondirected f-set order. The cluster property uses exactly the finite equilibria on these anchored f-sets, with no unrelated candidate measures.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 23, proof of Theorem 2 ('Indeed, fix i ...')

import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Proof of Theorem 2(ii), p. 23: an anchored f-set equilibrium family passes
condition (3) to any cluster point against continuous real test functions. -/
theorem cluster_point_is_ce {ι : Type*} [Nonempty ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (hh : ∀ i, Continuous (h i))
    (anchor : ∀ i, S i)
    (F : (∀ i, Finset (S i)) → Finset (∀ i, S i))
    (w : (∀ i, Finset (S i)) → (∀ i, S i) → ℝ)
    (hFw : ∀ T, IsAnchoredFSet anchor T → IsFSetCE h T (F T) (w T))
    (p : Measure (∀ i, S i)) (hp : IsProbabilityMeasure p)
    (hcluster : ∀ (f : C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet anchor T₀ →
        ∃ T, IsAnchoredFSet anchor T ∧ FSetLE T₀ T ∧
          |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε) :
    IsCorrelatedEq h p := by sorry

end HartSchmeidler.FinStrat
