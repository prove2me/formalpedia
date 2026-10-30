-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_appH_expected_improvement_identity
-- name    : KarimiPL.ProxCD.appH_expected_improvement_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:30.58982+00:00
-- url     : https://prove2.me/theorems/8df91dd8-8516-4fb6-b9ce-77d3136437d1
-- title:
--   Appendix H: expected coordinate improvement equals $-\mathcal D_g(x,L)/(2Ld)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Let $L > 0$ and $x \in \mathbb{R}^d$, and suppose that for every coordinate $i$ the number $t_i$ minimizes the coordinate model
--   $$m_i(x; t) = t\,\nabla_i f(x) + \frac{L}{2}t^2 + g_i(x_i + t) - g_i(x_i)$$
--   over $t$ with $x_i + t \in D_i$. Then:
--
--   1. the point $y = x + (t_1, \dots, t_d)$ attains the minimum in
--   $$\min_{y}\Big[\langle \nabla f(x), y - x\rangle + \frac L2\|y - x\|^2 + g(y) - g(x)\Big],$$
--   the minimum defining $\mathcal D_g(x, L)$ in (13);
--   2. the expected improvement of the coordinate model under a uniformly random coordinate satisfies
--   $$\frac1d \sum_{i=1}^d \min_{t} m_i(x; t) = -\frac{1}{2Ld}\,\mathcal D_g(x, L).$$
--
--   This is the unnumbered chain of equalities in Appendix H of Karimi, Nutini and Schmidt: separability of $g$ lets the sum of coordinate-wise minima be exchanged with the joint minimum over $y$, which links the expected coordinate step to $\mathcal D_g$, and hence to the proximal-PL inequality.
--
--   **Formalization Note** The identity is algebraic: it needs no smoothness of $f$, no convexity of the $g_i$, and no condition on $x$. At $d = 0$ both sides of item 2 are $0$.
--
--   Differences from the source:
--   - generalization: stated at an iterate x of the method under the standing assumptions of Appendix H → any x ∈ ℝᵈ and any d; no smoothness of f, no convexity of the gᵢ, no (12); reason: the chain of equalities uses only separability; the Lean statement specializes to the paper's
--   - encoding: min_{tᵢ} [tᵢ∇ᵢf(x) + (L/2)tᵢ² + gᵢ(xᵢ + tᵢ) − gᵢ(xᵢ)], the minimum presupposed to exist → numbers tᵢ attaining each minimum (IsCoordMin); the minima are the model values at tᵢ; reason: the paper's min is defined only when attained, and then its value is the model at a minimizer
--   - encoding: E{·} over a uniformly random coordinate i → the average (1/d) Σᵢ; reason: a uniform coordinate has probability 1/d each
--   - encoding: min_{y ≡ x + (t₁, …, t_d)} [⟨∇f(x), y − x⟩ + (L/2)‖y − x‖² + g(y) − g(x)] (third line) → clause (a): x + Σᵢ tᵢeᵢ is a minimizer of that bracket over dom g (IsProxGradStep), so Dg's infimum is this minimum; reason: the third line asserts that the joint minimum is the sum of coordinate minima, attained at y = x + (t₁, …, t_d)
--   - encoding: g(x) = Σᵢ gᵢ(xᵢ) separable, gᵢ : ℝ → (−∞, ∞] → effective domains Dc i and finite values gc i; g = sepG gc on dom g = sepDom Dc; reason: every separable extended-valued g has this form; same instances
--   - encoding: Lipschitz constant L (implicitly positive) → 0 < L; reason: the step size 1/L and the factor 1/(2L) require it
--   - reading: “1/n”, “−(1/(2Ln)) Dg(L, x)” → the intended objects: d, gᵢ(xᵢ), D_g(x, L); reason: typos on p. 23: n is the dimension d, g(xᵢ) is gᵢ(xᵢ) (the bracket of (16)), and D_g(L, x) is D_g(x, L) of (13) with the arguments swapped
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, Appendix H, unnumbered display, p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_sepDom
import Definitions.Def_KarimiPL_ProxCD_IsProxGradStep
import Definitions.Def_KarimiPL_ProxCD_Dg
import Definitions.Def_KarimiPL_ProxCD_coordModel
import Definitions.Def_KarimiPL_ProxCD_IsCoordMin

namespace KarimiPL.ProxCD

/-- **Appendix H: the expected coordinate improvement equals `−D_g(x, L)/(2Ld)`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, Appendix H, unnumbered display, p. 23:
"E{min_ti ti∇if(x) + (L/2)ti² + gi(xi + ti) − gi(xi)} = (1/n) Σi min_ti ti∇if(x) + (L/2)ti² +
gi(xi + ti) − gi(xi) = (1/n) min_{t1,··· ,tn} Σi ti∇if(x) + (L/2)ti² + gi(xi + ti) − gi(xi)
= (1/n) min_{y≡x+(t1,··· ,tn)} ⟨∇f(x), y − x⟩ + (L/2)||y − x||² + g(y) − g(x)
= −(1/(2Ln)) Dg(L, x). (Note that separability allows us to exchange the summation and
minimization operators.)"

If `L > 0` and, for every coordinate `i`, `tᵢ` minimizes the bracket of (16) in coordinate `i` at
`x`, then (a) `y = x + (t₁, …, t_d)` attains the minimum in `D_g(x, L)` (13) for the separable
`g = sepG gc` with domain `sepDom Dc`, and (b)
`(1/d) ∑ᵢ [tᵢ∇ᵢf(x) + (L/2)tᵢ² + gᵢ(xᵢ + tᵢ) − gᵢ(xᵢ)] = −(1/(2Ld)) D_g(x, L)`.

**Formalization Note.** The page writes `n` for the dimension `d` and `Dg(L, x)` for `D_g(x, L)`
(typos, not copied). The expectation over a uniform coordinate `i` is the average `(1/d) ∑ᵢ`.
Clause (a) is the third line of the display (the joint minimizer); clause (b) equates its first
and last lines. The identity is algebraic: no smoothness of `f`, no convexity of `gᵢ` and no
condition on `x` is needed. At `d = 0` both sides of (b) are `0`. -/
theorem appH_expected_improvement_identity {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L : ℝ} (hL : 0 < L)
    (x : EuclideanSpace ℝ (Fin d)) (t : Fin d → ℝ)
    (ht : ∀ i, IsCoordMin f gc Dc L i x (t i)) :
    IsProxGradStep f (sepG gc) (sepDom Dc) L x (x + ∑ i, EuclideanSpace.single i (t i)) ∧
      1 / (d : ℝ) * ∑ i, coordModel f gc L i x (t i) =
        -(1 / (2 * L * d)) * Dg f (sepG gc) (sepDom Dc) L x := by sorry

end KarimiPL.ProxCD
