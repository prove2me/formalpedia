-- Prove2me | Theorems.Thm_GradSampling_Conv_theorem_3_3
-- name    : GradSampling.Conv.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:31.697382+00:00
-- url     : https://prove2.me/theorems/5e9ee74d-76c1-4974-8df8-0a9690dd0101
-- title:
--   Theorem 3.3 (Lebourg mean value theorem), p. 760 — f(y) − f(x) = ⟨w, y − x⟩ with w ∈ ∂̄f(z), z ∈ [x, y]
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be locally Lipschitz and let $x,y\in\mathbb R^n$. Then there exist $z\in[x,y]$ and $w\in\bar\partial f(z)$ such that
--
--   $$f(y)-f(x)=\langle w,y-x\rangle .$$
--
--   The paper cites this from Clarke's monograph (Theorem 2.3.7) and applies it to the last failed trial step of the line search.
--
--   **Formalization Note** $[x,y]$ is the closed segment and $\bar\partial f$ is the published Clarke generalized gradient.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 760, Theorem 3.3 (citing Clarke 1983, Theorem 2.3.7)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- Theorem 3.3 (Lebourg mean value theorem), p. 760: for locally Lipschitz `f` and `x, y ∈ ℝⁿ` there
are `z ∈ [x, y]` and `w ∈ ∂̄f(z)` with `f(y) − f(x) = ⟨w, y − x⟩`. -/
theorem theorem_3_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∀ x y : EuclideanSpace ℝ (Fin n), ∃ z ∈ segment ℝ x y,
      ∃ w ∈ ClarkeGradients.Shared.generalizedGradient f z, f y - f x = inner ℝ w (y - x) := by sorry

end GradSampling.Conv
