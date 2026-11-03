-- Prove2me | Theorems.Thm_Grunbaum2003_convexHull_insert_inter_level_eq
-- name    : Grunbaum2003.convexHull_insert_inter_level_eq
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:34:26.675727+00:00
-- url     : https://prove2.me/theorems/1dde6446-f0b2-4468-80a2-6ccf8d5b36df
-- title:
--   Vertex-figure section as a hull of segment crossings
-- statement:
--   Let $v$ be a point of real $d$-space and $W$ a nonempty set. Suppose a continuous linear functional $\ell$ and a level $\alpha$ satisfy $\ell(w)<\alpha<\ell(v)$ for every $w\in W$. Then
--
--   $$\operatorname{conv}(\{v\}\cup W)\cap\ell^{-1}(\{\alpha\})=\operatorname{conv}\left\{v+\frac{\ell(v)-\alpha}{\ell(v)-\ell(w)}(w-v):w\in W\right\}.$$
--
--   No finiteness assumption on $W$ is needed. The crossing points provide the concrete vertex-figure generators used in the boundary-refinement induction.
-- source:
--   Vertex-figure construction in Grünbaum, On the facial structure of convex polytopes (1965), Theorem1* proof, pp.559–560. https://faculty.washington.edu/moishe/branko/BG52.Facial%20structure.pdf

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem convexHull_insert_inter_level_eq (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    convexHull ℝ (insert v W) ∩ l ⁻¹' {α} =
      convexHull ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) := by sorry

end Grunbaum2003
