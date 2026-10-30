-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_eq_62_coord_upper_bound
-- name    : KarimiPL.ProxCD.eq_62_coord_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:52.390473+00:00
-- url     : https://prove2.me/theorems/05de4a6e-cb37-474a-86bd-f566158ca1ef
-- title:
--   Eq. (62): coordinate-wise upper bound on $F(x + t e_i) - F(x)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Let $L \in \mathbb{R}$ and assume $f$ is coordinate-wise smooth with constant $L$ in the sense of (5):
--   $$f(x + \alpha e_i) \le f(x) + \alpha \nabla_i f(x) + \frac L2 \alpha^2 \quad \text{for all } x \in \mathbb{R}^d,\ \text{all coordinates } i,\ \text{all } \alpha \in \mathbb{R}.$$
--   Then for every $x \in \mathbb{R}^d$, every coordinate $i$ and every $t \in \mathbb{R}$,
--   $$F(x + t e_i) - F(x) \le t\,\nabla_i f(x) + \frac L2 t^2 + g_i(x_i + t) - g_i(x_i).$$
--
--   This is inequality (62) of Karimi, Nutini and Schmidt, the first step of the proof of Theorem 6 (Appendix H): the change of $F$ along one coordinate is bounded by the coordinate model that the update (16) minimizes.
--
--   **Formalization Note** $g = \sum_i g_i(x_i)$ is evaluated through its finite values, so the bound holds at every $x$; on $\operatorname{dom} g$ it is the paper's statement. Convexity of the $g_i$ is not needed.
--
--   Differences from the source:
--   - generalization: ∇f is coordinate-wise Lipschitz continuous → f differentiable and satisfying (5): f(x + αeᵢ) ≤ f(x) + α∇ᵢf(x) + (L/2)α² for all x, i, α, with the same L; reason: §3.1 (p. 5) defines coordinate-wise Lipschitz continuity by (5), so (5) itself covers every f the page means; (2) at y = x + αeᵢ implies (5), so the item applies under Theorem 6's hypothesis
--   - generalization: stated at points of dom g in the proof of Theorem 6 → any x ∈ ℝᵈ (no x ∈ dom g needed); reason: the inequality is an identity-based bound valid at every point; it specializes to the iterates x_k ∈ dom g
--   - encoding: g(x) = Σᵢ gᵢ(xᵢ) separable, gᵢ : ℝ → (−∞, ∞] → effective domains Dc i and finite values gc i; g = sepG gc on dom g = sepDom Dc; reason: every separable extended-valued g has this form; same instances
--   - reading: “g(xi)” in (62) → the intended objects: d, gᵢ(xᵢ), D_g(x, L); reason: typos on p. 23: n is the dimension d, g(xᵢ) is gᵢ(xᵢ) (the bracket of (16)), and D_g(L, x) is D_g(x, L) of (13) with the arguments swapped
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, Appendix H, eq. (62), p. 23 (with (5), §3.1, p. 5)

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_coordModel

namespace KarimiPL.ProxCD

/-- **Eq. (62): coordinate-wise upper bound on the change of `F = f + g`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, Appendix H, eq. (62), p. 23: "From coordinate-wise Lipschitz continuity of ∇f and
separability of g, we have F(x + yiei) − F(x) ≤ yi∇if(x) + (L/2)yi² + gi(xi + yi) − g(xi). (62)"

If `f` is differentiable and satisfies the coordinate-wise smoothness inequality (5) with
constant `L`, then for every `x`, coordinate `i` and `t ∈ ℝ`,
`F(x + t eᵢ) − F(x) ≤ t ∇ᵢf(x) + (L/2) t² + gᵢ(xᵢ + t) − gᵢ(xᵢ)`, where `F = f + sepG gc`.

**Formalization Note.** "Coordinate-wise Lipschitz continuity of ∇f" is (5) (§3.1, p. 5:
"f(x + αei) ≤ f(x) + α∇if(x) + (L/2)α², ∀α ∈ R, ∀x ∈ Rd, (5) for any coordinate i"), assumed
as the hypothesis `hcoord`; (2) implies it. The page's "g(xi)" is a typo for `gᵢ(xᵢ)`; the
Lean states `gc i (x i)`. The separable `g` is `sepG gc`; the inequality holds for every `x`
because `g(x + t eᵢ) − g(x) = gᵢ(xᵢ + t) − gᵢ(xᵢ)` is an identity of finite values (on
`dom g` it is the paper's statement). `t eᵢ` is `EuclideanSpace.single i t`. -/
theorem eq_62_coord_upper_bound {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {L : ℝ} (hf : Differentiable ℝ f)
    (hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (α : ℝ),
      f (x + EuclideanSpace.single i α) ≤ f x + α * gradient f x i + L / 2 * α ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (t : ℝ) :
    f (x + EuclideanSpace.single i t) + sepG gc (x + EuclideanSpace.single i t) -
        (f x + sepG gc x) ≤ coordModel f gc L i x t := by sorry

end KarimiPL.ProxCD
