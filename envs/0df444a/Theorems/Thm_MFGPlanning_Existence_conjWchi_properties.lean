-- Prove2me | Theorems.Thm_MFGPlanning_Existence_conjWchi_properties
-- name    : MFGPlanning.Existence.conjWchi_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:00:31.390572+00:00
-- url     : https://prove2.me/theorems/255f1f88-25a8-4ff7-82d3-9b0ec5af20f0
-- title:
--   §3.1, p. 7 — $V((0,\infty)) = (\lambda,\infty)$ and $(W+\chi)^*$ is real, convex, continuous, nondecreasing, with explicit values
-- statement:
--   Assume (24): $W:\mathbb R\to\mathbb R$ is strictly convex, superlinearly coercive and of class $C^2$, and $V = W'$. Then the image of $(0,+\infty)$ by $V$ is an interval $\mathcal J_V = (\lambda,+\infty)$, and the Legendre–Fenchel transform
--   $$(W+\chi)^*(a) = \sup_{m\ge0}\,[am - W(m)]$$
--   is finite, convex, continuous and nondecreasing on $\mathbb R$. Moreover,
--   $$(W+\chi)^*(a) = a\,V^{-1}(a) - W(V^{-1}(a)) \quad\text{if } a\in\mathcal J_V,\qquad (W+\chi)^*(a) = -W(0)\quad\text{if } a\le\lambda.$$
--
--   This gives the explicit form of the convex function out of which the dual functional $\Theta$ is built, and the interval $\mathcal J_V$ that reappears in the constraint qualification of Lemma 1.
--
--   **Formalization Note** The statement says there is a real function $\varphi$ equal to the `EReal`-valued $(W+\chi)^*$. "$a\in\mathcal J_V$, $m = V^{-1}(a)$" is written as "$m > 0$ and $V(m) = a$", which needs no inverse function; $V$ is injective on $(0,\infty)$ by strict convexity. Only (24) is assumed.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.1, p. 7, first paragraph

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid
import Definitions.Def_MFGPlanning_Existence_Hyp
import Definitions.Def_MFGPlanning_Existence_Duality

namespace MFGPlanning.Existence

/-- Achdou, Camilli, Capuzzo-Dolcetta, hal-00465404v1 (2010), §3.1, p. 7 (PDF 8), first paragraph:
under (24), the image of `(0, +∞)` by `V = W'` is an interval `J_V = (λ, +∞)`; `(W + χ)^*` is convex,
continuous and nondecreasing; `(W + χ)^*(α) = α V⁻¹(α) − W(V⁻¹(α))` for `α ∈ J_V` and
`(W + χ)^*(α) = −W(0)` for `α ∉ J_V`.

Formalization Note: `(W + χ)^*` is the `EReal` supremum `conjWchi`; the statement says it is a real
function `φ`. "`α ∈ J_V`, `m = V⁻¹(α)`" is written as `0 < m ∧ V m = α`, which needs no inverse. -/
theorem conjWchi_properties (d : Data) (hW : A24 d) :
    ∃ lam : ℝ, d.V '' Set.Ioi 0 = Set.Ioi lam ∧
      ∃ φ : ℝ → ℝ,
        (∀ a : ℝ, conjWchi d a = (φ a : EReal)) ∧
        ConvexOn ℝ Set.univ φ ∧ Continuous φ ∧ Monotone φ ∧
        (∀ a m : ℝ, 0 < m → d.V m = a → φ a = a * m - d.W m) ∧
        (∀ a : ℝ, a ≤ lam → φ a = -d.W 0) := by sorry

end MFGPlanning.Existence
