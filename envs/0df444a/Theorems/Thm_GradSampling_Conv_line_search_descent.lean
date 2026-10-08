-- Prove2me | Theorems.Thm_GradSampling_Conv_line_search_descent
-- name    : GradSampling.Conv.line_search_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:27.008231+00:00
-- url     : https://prove2.me/theorems/0eac16f3-6a5a-423e-9e12-de8ba53a1838
-- title:
--   §2, p. 756 — at x ∈ D with g ≠ 0 the direction d = −g/‖g‖ gives f(x+td) ≤ f(x)+tβ∇f(x)ᵀd ≤ f(x)−tβ‖g‖ for small t
-- statement:
--   Let $D\subseteq\mathbb R^n$ be open and $f$ continuously differentiable on $D$, let $\beta\in(0,1)$, $x\in D$ and $x^1,\dots,x^m\in\mathbb R^n$. Let $g$ be the least-norm element of
--   $G=\operatorname{conv}\{\nabla f(x),\nabla f(x^1),\dots,\nabla f(x^m)\}$ and suppose $g\neq0$; put $d=-g/\|g\|$. Then $\langle h,d\rangle\le-\|g\|$ for every $h\in G$ (in particular $\nabla f(x)^Td\le-\|g\|$), and there is $\bar t>0$ such that
--
--   $$f(x+td)\le f(x)+t\beta\,\nabla f(x)^Td\le f(x)-t\beta\|g\|\qquad\text{for all }t\in(0,\bar t).$$
--
--   This is why the Armijo line search of Step 3 of the GS algorithm is well defined.
--
--   **Formalization Note** The sampling points need not lie in $D$ for this claim, so that hypothesis is dropped.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 756, §2, the two displays after "recall from convex analysis" (the line search is well defined)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- §2, p. 756 (the display before Lemma 2.1's motivation): if `x ∈ D`, `g` is the least-norm element of
`G = conv{∇f(x), ∇f(x¹), …, ∇f(x^m)}` and `g ≠ 0`, then with `d = −g/‖g‖` every element of `G` has
`⟨h, d⟩ ≤ −‖g‖`, and there is `t̄ > 0` with
`f(x + t d) ≤ f(x) + tβ∇f(x)ᵀd ≤ f(x) − tβ‖g‖` for all `t ∈ (0, t̄)`. -/
theorem line_search_descent {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hC1 : ContDiffOn ℝ 1 f D) (β : ℝ) (hβ : β ∈ Set.Ioo 0 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) (pts : Fin m → EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n))
    (hg : IsMinNormIn g (sampleHull f x pts)) (hg0 : g ≠ 0) :
    (∀ h ∈ sampleHull f x pts, inner ℝ h (-(‖g‖⁻¹ • g)) ≤ -‖g‖) ∧
      ∃ tbar > 0, ∀ s ∈ Set.Ioo 0 tbar,
        f (x + s • -(‖g‖⁻¹ • g)) ≤ f x + s * β * inner ℝ (gradient f x) (-(‖g‖⁻¹ • g)) ∧
          f x + s * β * inner ℝ (gradient f x) (-(‖g‖⁻¹ • g)) ≤ f x - s * β * ‖g‖ := by sorry

end GradSampling.Conv
