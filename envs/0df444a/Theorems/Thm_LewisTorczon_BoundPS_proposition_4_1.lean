-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_proposition_4_1
-- name    : LewisTorczon.BoundPS.proposition_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:45:29.504788+00:00
-- url     : https://prove2.me/theorems/37bf404b-1f7b-4460-b768-41f733541e1a
-- title:
--   Proposition 4.1 — a descent direction shorter than $\omega(x,\varepsilon/2)$ decreases $f$ by $(\varepsilon/2)\|d\|$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $g=\nabla f$, $x,d\in\mathbb R^n$ and $\varepsilon>0$. For the modulus of continuity
--   $$\omega(x,\varepsilon)=\sup\{\delta>0 : \|g(y)-g(x)\|<\varepsilon\ \text{for all } y \text{ with } \|y-x\|<\delta\},$$
--   suppose that $f$ is continuously differentiable along the closed segment from $x$ to $x+d$, that $g(x)\ne0$, that $g(x)^{T}d\le-\varepsilon\|d\|$, and that $\|d\|<\omega(x,\varepsilon/2)$. Then
--   $$f(x+d)-f(x)\le-\frac{\varepsilon}{2}\,\|d\| .$$
--
--   This is the elementary descent estimate that turns a sufficiently short, sufficiently steep trial step into a guaranteed decrease of the objective.
--
--   **Formalization Note** The supremum $\omega$ is not formed. The hypothesis $\|d\|<\omega(x,\varepsilon/2)$ is stated in the equivalent form: there is $\delta$ with $\|d\|<\delta$ and $\|g(y)-g(x)\|<\varepsilon/2$ whenever $\|y-x\|<\delta$ (the set in the definition of $\omega$ is closed downward, so the two are equivalent; a real supremum of an unbounded set would evaluate to $0$ in Lean). "Continuously differentiable on the segment" is encoded as: $f$ is differentiable at every point of the closed segment and $\nabla f$ is continuous on it. The gradient is Mathlib's `gradient f`.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 8, Proposition 4.1; ω defined on p. 7, §4

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.1**, p. 8. Let `g = ∇f`. If `f` is differentiable at every point of the closed
segment `[x, x + d]` with `g` continuous on it, `g(x) ≠ 0`, `g(x)ᵀd ≤ -ε‖d‖`, and
`‖d‖ < ω(x, ε/2)` — encoded as: some `δ > ‖d‖` has `‖g(y) - g(x)‖ < ε/2` whenever `‖y - x‖ < δ` —
then `f(x + d) - f(x) ≤ -(ε/2)‖d‖`. -/
theorem proposition_4_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (ε δ : ℝ) (hε : 0 < ε)
    (hdiff : ∀ y ∈ segment ℝ x (x + d), DifferentiableAt ℝ f y)
    (hcont : ContinuousOn (gradient f) (segment ℝ x (x + d)))
    (hgx : gradient f x ≠ 0) (hdesc : inner ℝ (gradient f x) d ≤ -ε * ‖d‖)
    (hω : ∀ y, ‖y - x‖ < δ → ‖gradient f y - gradient f x‖ < ε / 2) (hd : ‖d‖ < δ) :
    f (x + d) - f x ≤ -(ε / 2) * ‖d‖ := by sorry

end LewisTorczon.BoundPS
