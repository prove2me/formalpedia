-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_appH_one_step_rate
-- name    : KarimiPL.ProxCD.appH_one_step_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:33.764459+00:00
-- url     : https://prove2.me/theorems/794092d9-385d-4908-afa5-ad6a7512fd60
-- title:
--   Appendix H: one-step expected contraction by $1 - \mu/(dL)$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Assume:
--
--   1. $d \ge 1$, $L > 0$, and $f$ satisfies the coordinate-wise smoothness inequality (5) with constant $L$;
--   2. $x^* \in \operatorname{dom} g$ minimizes $F$, and $F^* = F(x^*)$;
--   3. $(f, g)$ satisfies the proximal-PL inequality (12) with constant $\mu > 0$: $\frac12\mathcal D_g(x, L) \ge \mu(F(x) - F^*)$ wherever the minimum in $\mathcal D_g(x, L)$ is attained.
--
--   Let $x \in \operatorname{dom} g$, and for every coordinate $i$ let $t_i$ minimize $t\,\nabla_i f(x) + \frac L2 t^2 + g_i(x_i + t) - g_i(x_i)$ over $x_i + t \in D_i$. Then
--   $$\frac1d \sum_{i=1}^d \big[F(x + t_i e_i) - F^*\big] \le \Big(1 - \frac{\mu}{dL}\Big)\big[F(x) - F^*\big],$$
--   i.e. $\mathbb E[F(x_{k+1}) - F^*] \le (1 - \mu/(dL))[F(x_k) - F^*]$ given $x_k = x$, with $i_k$ uniform.
--
--   This is the closing sentence of Appendix H of Karimi, Nutini and Schmidt; applied along the iterates and combined with iterated expectations it gives the rate (17) of Theorem 6. $f$ need not be convex, the $g_i$ need not be closed, and $\mu \le dL$ is not assumed.
--
--   Differences from the source:
--   - generalization: ∇f is coordinate-wise Lipschitz continuous → f differentiable and satisfying (5): f(x + αeᵢ) ≤ f(x) + α∇ᵢf(x) + (L/2)α² for all x, i, α, with the same L; reason: §3.1 (p. 5) defines coordinate-wise Lipschitz continuity by (5), so (5) itself covers every f the page means; (2) at y = x + αeᵢ implies (5), so the item applies under Theorem 6's hypothesis
--   - generalization: proximal-PL inequality (12) at every x → (12) required only at x ∈ dom g where the minimum in (13) is attained (IsProxPL); reason: off dom g (12) reads +∞ ≥ +∞, and where the minimum is not attained (13) is undefined; the Lean hypothesis is implied by the paper's, and every iterate has an attained minimum (milestone appH_expected_improvement_identity)
--   - encoding: g(x) = Σᵢ gᵢ(xᵢ) separable, each gᵢ : ℝ → (−∞, ∞] convex → effective domains Dc i and finite values gc i with ConvexOn ℝ (Dc i) (gc i); g = sepG gc on dom g = sepDom Dc; reason: every separable g with convex extended-valued gᵢ has this form and conversely; same instances; g convex follows from the gᵢ and is not added
--   - encoding: F has a non-empty solution set X*, optimal value F* → x* ∈ dom g with F(x*) ≤ F(z) for all z ∈ dom g, and F* = F(x*); reason: F = +∞ off dom g, so the minimizers of F are exactly these points
--   - encoding: E[F(x_{k+1})] over i_k uniform, given x_k → (1/d) Σᵢ F(x + tᵢeᵢ) with tᵢ a minimizer of the bracket of (16) in coordinate i at x; reason: given x_k = x, the coordinate step in coordinate i lands at x + tᵢeᵢ, each with probability 1/d
--   - encoding: d coordinates and Lipschitz constant L (implicitly positive) → 0 < d and 0 < L; reason: uniform selection among d coordinates needs d ≥ 1, and the step 1/L and the ratio µ/(dL) need L > 0
--   - reading: “(1 − µ/(nL))” → the intended objects: d, gᵢ(xᵢ), D_g(x, L); reason: typos on p. 23: n is the dimension d, g(xᵢ) is gᵢ(xᵢ) (the bracket of (16)), and D_g(L, x) is D_g(x, L) of (13) with the arguments swapped
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, Appendix H, closing sentence, p. 23

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_sepDom
import Definitions.Def_KarimiPL_ProxCD_IsProxPL
import Definitions.Def_KarimiPL_ProxCD_IsCoordMin

namespace KarimiPL.ProxCD

/-- **Appendix H, closing sentence: one-step expected contraction by `1 − µ/(dL)`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, Appendix H, p. 23: "Subtracting F∗ from both sides and applying the proximal-PL
inequality yields a linear convergence rate of (1 − µ/(nL))."

Let `d ≥ 1`, `L > 0`, `f` differentiable with the coordinate-wise smoothness inequality (5),
`gᵢ` convex with effective domains `Dc i`, `x* ∈ dom g` a minimizer of `F = f + g` over
`dom g` with `F* = F(x*)`, and `(f, g)` satisfying the proximal-PL inequality (12) with
constant `µ`. Then for every `x ∈ dom g` and minimizers `tᵢ` of the bracket of (16) in each
coordinate `i` at `x`,
`(1/d) ∑ᵢ [F(x + tᵢ eᵢ) − F*] ≤ (1 − µ/(dL)) [F(x) − F*]`,
i.e. `E[F(x_{k+1}) − F*] ≤ (1 − µ/(dL)) [F(x_k) − F*]` given `x_k = x`, `i_k` uniform.

**Formalization Note.** The page writes `n` for `d` (typo, not copied). "Coordinate-wise
Lipschitz continuity" (Appendix H's hypothesis) is (5) (§3.1, p. 5), the hypothesis `hcoord`.
`g = sepG gc` on `dom g = sepDom Dc`; `F* = f xstar + sepG gc xstar`. No convexity of `f`, no
closedness of `gᵢ` and no `µ ≤ dL` is assumed. -/
theorem appH_one_step_rate {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L μ : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hf : Differentiable ℝ f)
    (hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (α : ℝ),
      f (x + EuclideanSpace.single i α) ≤ f x + α * gradient f x i + L / 2 * α ^ 2)
    (hg : ∀ i, ConvexOn ℝ (Dc i) (gc i))
    {xstar : EuclideanSpace ℝ (Fin d)} (hxD : xstar ∈ sepDom Dc)
    (hmin : ∀ z ∈ sepDom Dc, f xstar + sepG gc xstar ≤ f z + sepG gc z)
    (hPL : IsProxPL f (sepG gc) (sepDom Dc) L μ xstar)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ sepDom Dc) (t : Fin d → ℝ)
    (ht : ∀ i, IsCoordMin f gc Dc L i x (t i)) :
    1 / (d : ℝ) * ∑ i, (f (x + EuclideanSpace.single i (t i)) +
        sepG gc (x + EuclideanSpace.single i (t i)) - (f xstar + sepG gc xstar)) ≤
      (1 - μ / (d * L)) * (f x + sepG gc x - (f xstar + sepG gc xstar)) := by sorry

end KarimiPL.ProxCD
