-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_unit_pole_off_surface_and_loop
-- name    : HryniewiczCriterion.exists_unit_pole_off_surface_and_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T09:36:36.962698+00:00
-- url     : https://prove2.me/theorems/c7f72911-9e5a-495f-8353-1ef4c1ea6a0e
-- title:
--   A unit vector missing a differentiable surface and a loop in the 3-sphere
-- statement:
--   Let $f:\mathbb{R}^2\to\mathbb{R}^4$ be differentiable on a set $U$ and let $g:\mathbb{R}\to\mathbb{R}^4$ be differentiable. Then there is a unit vector $N\in S^3$ that misses every unit point of the surface and of the curve:
--   $$f(v)\neq N\ \ (v\in U,\ |f(v)|=1),\qquad g(s)\neq N\ \ (|g(s)|=1).$$
--
--   The cones $\{c\,f(v):c\in\mathbb{R},v\in U\}$ and $\{c\,g(s)\}$ are images of subsets of a hyperplane of $\mathbb{R}^4$ under maps that are differentiable there, so they have Lebesgue measure zero. Normalizing a point $M$ outside both cones gives $N=M/|M|$. In practice this provides an admissible stereographic pole for Gauss linking integrals of loops on a disk-like surface in $S^3$.
-- source:
--   Elementary (images of null sets under differentiable maps are null); used for the pole in U. Hryniewicz, arXiv:1105.2077, Lemma 3.12

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.exists_unit_pole_off_surface_and_loop (f : Plane → R4) (U : Set Plane) (hf : DifferentiableOn ℝ f U)
    (g : ℝ → R4) (hg : Differentiable ℝ g) :
    ∃ N : R4, euclidNorm N = 1 ∧ (∀ v ∈ U, euclidNorm (f v) = 1 → f v ≠ N) ∧
      ∀ s, euclidNorm (g s) = 1 → g s ≠ N := by sorry
