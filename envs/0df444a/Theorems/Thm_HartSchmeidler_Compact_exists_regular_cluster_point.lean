-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_exists_regular_cluster_point
-- name    : HartSchmeidler.Compact.exists_regular_cluster_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:57:50.551515+00:00
-- url     : https://prove2.me/theorems/9fa74112-31b8-4136-a442-23fbc69c121c
-- title:
--   Proof of Theorem 3, p. 24 — a net of probability measures on a compact Hausdorff space has a regular cluster point
-- statement:
--   Let $X$ be a compact Hausdorff space with its Borel σ-algebra, let $D$ be a nonempty directed set, and let $(q_d)_{d\in D}$ be a net of probability measures on $X$. Then there is a **regular** probability measure $p$ on $X$ that is a cluster point of the net in the topology induced by the continuous functions $C(X)$: for every finite family $f_1,\dots,f_m\in C(X)$, every $\varepsilon>0$ and every $d_0\in D$ there is $d\ge d_0$ with
--   $$
--   \Bigl|\int_X f_k\,dp-\int_X f_k\,dq_d\Bigr|<\varepsilon\qquad(k=1,\dots,m).
--   $$
--
--   In the proof of Theorem 3 this is applied with $X=S$ (compact Hausdorff by Tychonoff), $D$ the f-sets containing a fixed profile, ordered by inclusion, and $q_T$ the correlated equilibria of the games $\Gamma_T$; the paper obtains $p$ from the Banach–Alaoglu theorem in the unit ball of $\mathrm{rca}(S)$, the dual of $C(S)$.
--
--   **Formalization Note** The cluster-point property is written out with finitely many test functions, which is exactly cluster-point convergence for the weak-* topology induced by $C(X)$. Regularity is Mathlib's `Measure.Regular` (outer regular, and inner regular by compact sets on open sets).
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 24, proof of Theorem 3 ("The net {q_T: T an f-set} (ordered by inclusion of the sets T) belongs to the unit ball of rca(S)"); https://doi.org/10.1287/moor.14.1.18

import Mathlib

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 24 (Banach–Alaoglu step): on a compact Hausdorff space with its Borel
σ-algebra, every net of probability measures indexed by a nonempty directed set has a cluster
point, for the topology induced by the continuous functions, that is a regular probability
measure. -/
theorem exists_regular_cluster_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure X) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure X, IsProbabilityMeasure p ∧ p.Regular ∧
      ∀ (fs : Finset C(X, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D, ∃ d : D, d₀ ≤ d ∧
        ∀ f ∈ fs, |∫ x, f x ∂p - ∫ x, f x ∂(q d)| < ε := by sorry

end HartSchmeidler.Compact
