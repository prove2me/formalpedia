-- Prove2me | Theorems.Thm_HartSchmeidler_FinStrat_exists_cluster_point
-- name    : HartSchmeidler.FinStrat.exists_cluster_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:09:10.344697+00:00
-- url     : https://prove2.me/theorems/9f1a6274-034a-4d6e-9041-f23409abf3c8
-- title:
--   Proof of Theorem 2(ii) — a weak cluster point of the f-set equilibria
-- statement:
--   Let $S$ be a product of nonempty finite discrete strategy spaces, indexed by an arbitrary nonempty player set. Give $S$ its product topology and product σ-algebra. For any nonempty directed preorder $D$ and family $(q_d)_{d\in D}$ of countably additive probability measures on $S$, there is a probability measure $p$ such that every weak neighborhood of $p$, tested by finitely many continuous real functions, contains $q_d$ at arbitrarily late indices. Explicitly, for every finite $A\subseteq C(S,\mathbb R)$, $\varepsilon>0$, and $d_0\in D$, some $d\ge d_0$ satisfies
--
--   $$\left|\int f,dp-\int f,dq_d\right|<\varepsilon\qquad(f\in A).$$
--
--   This is the cluster-point step of Theorem 2(ii), applied to the equilibrium measures $q_T$ from the finite f-set games.
--
--   **Formalization Note.** The proof uses f-sets containing one fixed profile $\hat s$; they are directed and can include any prescribed finite set of actions at finitely many coordinates. The paper's order of all f-sets is not directed. Finite collections of tests express a genuine weak neighborhood. The measure is on $\Sigma_0$, not the possibly larger Borel σ-algebra of an uncountable product.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 23, proof of Theorem 2 (net and cluster point; part (ii))

import Definitions.Def_HartSchmeidler_FinStrat_Game

namespace HartSchmeidler.FinStrat

open MeasureTheory

/-- Proof of Theorem 2(ii), p. 23: a directed family of probability measures on
the compact product has a cluster point for the weak topology induced by C(S).
Finite collections of tests describe a genuine weak neighborhood. -/
theorem exists_cluster_point {ι : Type*} [Nonempty ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    [∀ i, TopologicalSpace (S i)] [∀ i, DiscreteTopology (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, DiscreteMeasurableSpace (S i)]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure (∀ i, S i)) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure (∀ i, S i), IsProbabilityMeasure p ∧
      ∀ (fs : Finset C(∀ i, S i, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D,
        ∃ d : D, d₀ ≤ d ∧
          ∀ f ∈ fs, |∫ s, f s ∂p - ∫ s, f s ∂(q d)| < ε := by sorry

end HartSchmeidler.FinStrat
