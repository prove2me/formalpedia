-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_prop1_d
-- name    : MifflinSemismooth.Composition.prop1_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:34.819218+00:00
-- url     : https://prove2.me/theorems/6658e85a-7170-4552-a6fe-c76a74b08219
-- title:
--   Proposition 1(d) — boundedness and upper semicontinuity of generalized gradients
-- statement:
--   Let $F$ be Lipschitz with constant $K$ on an open set $B$, and let $x_k\in B$ converge to $x\in B$. If $g_k\in\partial F(x_k)$ for every $k$, then
--
--   $$\|g_k\|\le K\quad\text{for every }k,\qquad g\in\partial F(x)\quad\text{for every accumulation point }g\text{ of }(g_k). $$
--
--   Thus the generalized-gradient map is locally bounded and upper semicontinuous in the sequence sense used in the paper.
--
--   **Formalization Note** The paper's positive Lipschitz constant is represented by `NNReal`, which can always be enlarged to a positive one.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 1(d)

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Composition

theorem prop1_d {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : IsOpen B)
    (K : NNReal) (hFB : LipschitzOnWith K F B)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ B) :
    ∀ (xs gs : ℕ → EuclideanSpace ℝ (Fin n)),
      (∀ k, xs k ∈ B) → Tendsto xs atTop (𝓝 x) →
      (∀ k, gs k ∈ MifflinSemismooth.Extremal.genGrad F (xs k)) →
      (∀ k, ‖gs k‖ ≤ K) ∧
        ∀ g, MapClusterPt g atTop gs → g ∈ MifflinSemismooth.Extremal.genGrad F x := by sorry

end MifflinSemismooth.Composition
