-- Prove2me | Theorems.Thm_LG2021_nearby_simplex_volume
-- name    : LG2021.nearby_simplex_volume
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:26:14.468689+00:00
-- url     : https://prove2.me/theorems/0f739f01-97fc-4cbd-b3e3-9aed8532440f
-- title:
--   Nearby simplex volume (Lattimore–György, Lemma 7)
-- statement:
--   Let $d\ge1$ and let $K\subseteq\mathbb R^d$ be convex and contain the closed Euclidean unit ball. Suppose $D>0$ bounds every distance between two points of $K$, and $0<\delta\le D$. For each $x\in K$ there are distinct vertices $v_0,\ldots,v_d\in K$ with $v_0=x$ and $\|v_i-x\|_2\le\delta$, satisfying
--   $$\operatorname{vol}\!\left(\operatorname{conv}\{v_0,\ldots,v_d\}\right)\ge \left(\frac{\delta}{D}\right)^d\frac{(3/4)^{(d-1)/2}}{2d!}.$$
--   This is the nearby simplex used in the bandit stage-count argument. The source slice, number of vertices, homothety, and volume lower bound are preserved. The proof uses a triangular determinant for the base simplex rather than a maximization over regular simplices.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Appendix B, Lemma 7, printed p. 16.

import Mathlib
open MeasureTheory Set

theorem LG2021.nearby_simplex_volume {d : ℕ} (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hcv : Convex ℝ K)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ K)
    {D δ : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) :
    ∃ v : Fin (d + 1) → EuclideanSpace ℝ (Fin d), Function.Injective v ∧ v 0 = x ∧
      (∀ i, v i ∈ K) ∧ (∀ i, dist x (v i) ≤ δ) ∧
      ENNReal.ofReal ((δ / D)^d * (Real.sqrt (3 / 4))^(d - 1) / (2 * (d.factorial : ℝ))) ≤
        volume (convexHull ℝ (range v)) := by sorry
