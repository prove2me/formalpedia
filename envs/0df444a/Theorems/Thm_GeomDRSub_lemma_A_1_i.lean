-- Prove2me | Theorems.Thm_GeomDRSub_lemma_A_1_i
-- name    : GeomDRSub.lemma_A_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:04.715985+00:00
-- url     : https://prove2.me/theorems/e98f41f9-925b-43ef-b677-ba337c5b7b07
-- title:
--   Lemma A.1(i) — fundamental theorem of calculus on segments of the closed cube
-- statement:
--   Let $f:[0,1]^d\to\mathbb R$ be continuously differentiable, with gradient continuously extended to the boundary. Then for all $a,b\in[0,1]^d$,
--   $$
--   f(b)-f(a)=\int_0^1\big\langle\nabla f\big(a+t(b-a)\big),\,b-a\big\rangle\,dt .
--   $$
--   The segment may run along the boundary of the cube, where the gradient is the boundary extension. The identity is used to express increments of $f$ along the coordinate paths through averaged partial derivatives.
--
--   Differences from the source:
--   - encoding: f : [0,1]^d → ℝ continuously differentiable, gradient continuously extended to the boundary → f : ℝ^d → ℝ with ContDiffOn ℝ 1 f (cube d), gradient = within-cube derivative gradQ; reason: only the values on the cube matter; for d ≥ 1 the within-cube derivative is the continuous extension of the interior gradient
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma A.1(i), p.65, Eq. (269)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_gradQ

namespace GeomDRSub

/-- **Lemma A.1(i) (fundamental theorem of calculus on segments of the closed cube).**
Aggarwal–Lu, arXiv:2610.00545, Appendix A, p.65: "Let `f : [0, 1]^d → ℝ` be continuously
differentiable, with gradient continuously extended to the boundary. For any `a, b ∈ [0, 1]^d`,
`f(b) − f(a) = ∫₀¹ ⟨∇f(a + t(b − a)), b − a⟩ dt`. (269)"

**Formalization Note.** "Continuously differentiable with gradient continuously extended to the
boundary" is `ContDiffOn ℝ 1 f (cube d)`, and `∇f` is the within-cube gradient `gradQ f`. The
segment from `a` to `b` may run along the boundary of the cube. -/
theorem lemma_A_1_i {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiffOn ℝ 1 f (cube d))
    (a b : EuclideanSpace ℝ (Fin d)) (ha : a ∈ cube d) (hb : b ∈ cube d) :
    f b - f a = ∫ t in (0 : ℝ)..1, inner ℝ (gradQ f (a + t • (b - a))) (b - a) := by sorry

end GeomDRSub
