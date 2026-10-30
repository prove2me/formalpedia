-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_eq_63_expected_decrease
-- name    : KarimiPL.ProxCD.eq_63_expected_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:58.20898+00:00
-- url     : https://prove2.me/theorems/cc112f77-1908-4410-a1a0-b9e769746c64
-- title:
--   Eq. (63): expected decrease $\mathbb E[F(x_{k+1})] \le F(x_k) - \mathcal D_g(x_k,L)/(2Ld)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Let $d \ge 1$, $L > 0$, and assume $f$ satisfies the coordinate-wise smoothness inequality (5) with constant $L$. Let $x \in \mathbb{R}^d$, and for every coordinate $i$ let $t_i$ minimize $t\,\nabla_i f(x) + \frac L2 t^2 + g_i(x_i + t) - g_i(x_i)$ over $x_i + t \in D_i$, so that $x + t_i e_i$ is the proximal coordinate step (16) from $x$ in coordinate $i$. Then
--   $$\frac1d \sum_{i=1}^d F(x + t_i e_i) \le F(x) - \frac{1}{2Ld}\,\mathcal D_g(x, L).$$
--   The left side is $\mathbb E[F(x_{k+1})]$ given $x_k = x$ when $i_k$ is uniform on the $d$ coordinates.
--
--   This is inequality (63) of Karimi, Nutini and Schmidt, obtained by averaging (62) over the coordinate and applying the Appendix H identity. Combined with the proximal-PL inequality it yields the one-step contraction behind Theorem 6.
--
--   **Formalization Note** The inequality is stated at every $x$; on $\operatorname{dom} g$ it is the paper's.
--
--   Differences from the source:
--   - generalization: ∇f is coordinate-wise Lipschitz continuous → f differentiable and satisfying (5): f(x + αeᵢ) ≤ f(x) + α∇ᵢf(x) + (L/2)α² for all x, i, α, with the same L; reason: §3.1 (p. 5) defines coordinate-wise Lipschitz continuity by (5), so (5) itself covers every f the page means; (2) at y = x + αeᵢ implies (5), so the item applies under Theorem 6's hypothesis
--   - generalization: stated at the iterate x_k ∈ dom g → any x ∈ ℝᵈ (no x ∈ dom g needed); reason: the inequality is an identity-based bound valid at every point; it specializes to the iterates x_k ∈ dom g
--   - encoding: g(x) = Σᵢ gᵢ(xᵢ) separable, gᵢ : ℝ → (−∞, ∞] → effective domains Dc i and finite values gc i; g = sepG gc on dom g = sepDom Dc; reason: every separable extended-valued g has this form; same instances
--   - encoding: E[F(x_{k+1})] over i_k uniform, given x_k → (1/d) Σᵢ F(x + tᵢeᵢ) with tᵢ a minimizer of the bracket of (16) in coordinate i at x; reason: given x_k = x, the coordinate step in coordinate i lands at x + tᵢeᵢ, each with probability 1/d
--   - encoding: d coordinates and Lipschitz constant L (implicitly positive) → 0 < d and 0 < L; reason: uniform selection among d coordinates needs d ≥ 1, and the step 1/L and the ratio µ/(dL) need L > 0
--   - reading: “1/(2Ln)”, “Dg(L, x)” in (63) → the intended objects: d, gᵢ(xᵢ), D_g(x, L); reason: typos on p. 23: n is the dimension d, g(xᵢ) is gᵢ(xᵢ) (the bracket of (16)), and D_g(L, x) is D_g(x, L) of (13) with the arguments swapped
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, Appendix H, eq. (63), p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_sepDom
import Definitions.Def_KarimiPL_ProxCD_Dg
import Definitions.Def_KarimiPL_ProxCD_IsCoordMin

namespace KarimiPL.ProxCD

/-- **Eq. (63): expected decrease of `F` in one randomized proximal coordinate step.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, Appendix H, eq. (63), p. 23: "By using this and taking the expectation of (62) we get
E[F(xk+1)] ≤ F(xk) − (1/(2Ln)) Dg(L, x). (63)"

Let `d ≥ 1`, `L > 0`, `f` differentiable with the coordinate-wise smoothness inequality (5), and
`x ∈ ℝᵈ`. If `tᵢ` minimizes the bracket of (16) in coordinate `i` at `x` for every `i`, then
`(1/d) ∑ᵢ F(x + tᵢ eᵢ) ≤ F(x) − (1/(2Ld)) D_g(x, L)`, where `F = f + sepG gc`. The left side is
`E[F(x_{k+1})]` given `x_k = x`, with `i_k` uniform on the `d` coordinates.

**Formalization Note.** The page writes `n` for `d` and `Dg(L, x)` for `D_g(x_k, L)` (typos,
not copied). "Coordinate-wise Lipschitz continuity" is (5) (§3.1, p. 5), the hypothesis
`hcoord`; (2) implies it. The expectation over `i_k` is the average `(1/d) ∑ᵢ`; `0 < d` is
needed for it to be an average. The inequality holds for every `x` (on `dom g` it is the
paper's). -/
theorem eq_63_expected_decrease {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hf : Differentiable ℝ f)
    (hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (α : ℝ),
      f (x + EuclideanSpace.single i α) ≤ f x + α * gradient f x i + L / 2 * α ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (t : Fin d → ℝ)
    (ht : ∀ i, IsCoordMin f gc Dc L i x (t i)) :
    1 / (d : ℝ) * ∑ i, (f (x + EuclideanSpace.single i (t i)) +
        sepG gc (x + EuclideanSpace.single i (t i))) ≤
      f x + sepG gc x - 1 / (2 * L * d) * Dg f (sepG gc) (sepDom Dc) L x := by sorry

end KarimiPL.ProxCD
