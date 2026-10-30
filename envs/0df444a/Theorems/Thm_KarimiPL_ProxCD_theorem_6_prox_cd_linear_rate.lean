-- Prove2me | Theorems.Thm_KarimiPL_ProxCD_theorem_6_prox_cd_linear_rate
-- name    : KarimiPL.ProxCD.theorem_6_prox_cd_linear_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:30.455023+00:00
-- url     : https://prove2.me/theorems/32c895fb-4a8b-4d79-b505-057c541021af
-- title:
--   Theorem 6: linear convergence of randomized proximal coordinate descent under the proximal-PL inequality
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product and norm, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g(x) = \sum_{i=1}^d g_i(x_i)$ separable, each $g_i : \mathbb{R} \to (-\infty, +\infty]$ convex with effective domain $D_i$; $\operatorname{dom} g = D_1 \times \dots \times D_d$.
--
--   Assume:
--
--   1. $d \ge 1$, $L > 0$, and $f$ satisfies the quadratic upper bound (2): for all $x, y \in \mathbb{R}^d$,
--   $$f(y) \le f(x) + \langle \nabla f(x), y - x\rangle + \frac L2 \|y - x\|^2;$$
--   2. $x^* \in \operatorname{dom} g$ minimizes $F$, and $F^* = F(x^*)$;
--   3. $(f, g)$ satisfies the proximal-PL inequality with constant $\mu > 0$: $\frac12\mathcal D_g(x, L) \ge \mu(F(x) - F^*)$ wherever the minimum in $\mathcal D_g(x, L)$ is attained, where
--   $$\mathcal D_g(x,\alpha) = -2\alpha \min_{y} \Big[ \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x) \Big];$$
--   4. starting from $x_0 \in \operatorname{dom} g$, the coordinate-wise proximal-gradient method (16) is run with coordinates $i_0, i_1, \dots$ chosen independently and uniformly at random:
--   $$x_{k+1} = x_k + \alpha^* e_{i_k}, \qquad \alpha^* \in \operatorname*{argmin}_\alpha \Big[\alpha\nabla_{i_k} f(x_k) + \frac L2 \alpha^2 + g_{i_k}(x_{k,i_k} + \alpha) - g_{i_k}(x_{k,i_k})\Big].$$
--
--   $f$ need not be convex, the $g_i$ need not be closed, and $\mu \le dL$ is not assumed. Then for every $k \ge 0$
--   $$\mathbb E\big[F(x_k) - F^*\big] \le \Big(1 - \frac{\mu}{dL}\Big)^k \big[F(x_0) - F^*\big],$$
--   where the expectation is over the coordinates $i_0, \dots, i_{k-1}$.
--
--   This is Theorem 6 of Karimi, Nutini and Schmidt, eq. (17). It gives a global linear rate for randomized proximal coordinate descent without strong convexity, covering for example $\ell_1$-regularized least squares and box-constrained problems such as the SVM dual.
--
--   **Formalization Note** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla$ is Mathlib's `gradient`. The iterates are indexed by histories $s \in (\texttt{Fin } d)^k$, and the expectation is written as the average $d^{-k}\sum_s$ over all histories.
--
--   Differences from the source:
--   - generalization: f has an L-Lipschitz continuous gradient (2) → f differentiable and satisfying inequality (2) for all x, y; reason: an L-Lipschitz gradient implies (2) (milestone eq_2_descent_lemma), so the Lean statement specializes to the literal reading
--   - generalization: proximal-PL inequality (12) at every x → (12) required only at x ∈ dom g where the minimum in (13) is attained (IsProxPL); reason: off dom g (12) reads +∞ ≥ +∞, and where the minimum is not attained (13) is undefined; the Lean hypothesis is implied by the paper's, and every iterate has an attained minimum (milestone appH_expected_improvement_identity)
--   - encoding: g(x) = Σᵢ gᵢ(xᵢ) separable, each gᵢ : ℝ → (−∞, ∞] convex → effective domains Dc i and finite values gc i with ConvexOn ℝ (Dc i) (gc i); g = sepG gc on dom g = sepDom Dc; reason: every separable g with convex extended-valued gᵢ has this form and conversely; same instances; g convex follows from the gᵢ and is not added
--   - reading: x_{k+1} = argmin_α [α∇_{i_k}f(x_k) + (L/2)α² + g_{i_k}(x_{i_k} + α) − g_{i_k}(x_{i_k})] (16) → x (k+1) s = x k (init s) + α* e_{i_k} with α* a minimizer of that bracket over x_{i_k} + α ∈ Dc i_k (IsCoordProxStep, IsProxCDRun); reason: the printed (16) sets the vector x_{k+1} equal to the minimizing scalar; the coordinate update (6) on p. 5 and Appendix H (F(x + yᵢeᵢ) at the minimizing yᵢ) fix the meaning; the run asks a minimizer only at the points it visits, which the paper's (16) presupposes (it is unique there, the bracket being L-strongly convex on its domain), and adds no closedness of the gᵢ
--   - encoding: E[F(x_k) − F*] with i_k selected uniformly at random → d^{−k} Σ over all histories s ∈ (Fin d)^k of F(x_k(s)) − F*, with x_k(s) the iterate along the history s; reason: with i₀, i₁, … independent and uniform, x_k is a function of the history and every history has probability d^{−k}; the finite average is the expectation exactly
--   - encoding: F has a non-empty solution set X*, optimal value F* → x* ∈ dom g with F(x*) ≤ F(z) for all z ∈ dom g, and F* = F(x*); reason: F = +∞ off dom g, so the minimizers of F are exactly these points
--   - encoding: initial point x₀ unrestricted → x0 ∈ sepDom Dc; reason: for x₀ ∉ dom g the right-hand side (1 − µ/(dL))^k[F(x₀) − F*] is +∞ or the undefined 0·∞, so the paper's claim has no content there; without x0 ∈ dom g the junk real value of g(x₀) makes the Lean claim false (d = 1, f ≡ 0, L = 1, Dc = [0, 1], gc = 0 on [0, 1], gc(2) = −5, x* = 0, µ = 1/2, x₀ = 2, x₁ = 1: at k = 1 it reads 0 ≤ −5/2)
--   - encoding: d coordinates and Lipschitz constant L (implicitly positive) → 0 < d and 0 < L; reason: uniform selection among d coordinates needs d ≥ 1, and the step 1/L and the ratio µ/(dL) need L > 0
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, Theorem 6, eq. (16)–(17), p. 10 (setup of Theorem 5, p. 8; proof Appendix H, p. 23)

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_sepDom
import Definitions.Def_KarimiPL_ProxCD_IsProxPL
import Definitions.Def_KarimiPL_ProxCD_IsProxCDRun

open scoped InnerProductSpace

namespace KarimiPL.ProxCD

/-- **Theorem 6: linear convergence of randomized proximal coordinate descent under the
proximal-PL inequality.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, Theorem 6, p. 10: "Assume the setup of Theorem 5 and that g is a separable function
g(x) = Σi gi(xi), where each gi is convex. Then the coordinate-wise proximal-gradient update rule
(16) achieves a convergence rate E[F(xk) − F∗] ≤ (1 − µ/(dL))^k [F(x0) − F∗], (17) when ik is
selected uniformly at random." The setup of Theorem 5 (p. 8): "f has an L-Lipschitz continuous
gradient (2), F has a non-empty solution set X∗, g is convex, and F satisfies the proximal-PL
inequality (12)". Proof: Appendix H, p. 23.

For every `k ≥ 0`,
`d^{−k} ∑_{s ∈ (Fin d)^k} [F(x_k(s)) − F*] ≤ (1 − µ/(dL))^k [F(x₀) − F*]`,
where `x_k(s)` is the `k`-th iterate of (16) along the coordinate history `s = (i₀, …, i_{k−1})`.

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, `∇` is Mathlib's `gradient`.
Smoothness is (2) itself (`hsmooth`), which an `L`-Lipschitz gradient implies
(`eq_2_descent_lemma`). The separable extended-valued `g = ∑ᵢ gᵢ(xᵢ)` is encoded by effective
domains `Dc i` and finite values `gc i` with `ConvexOn ℝ (Dc i) (gc i)`; `dom g = sepDom Dc`,
`g = sepG gc` on it. No closedness or lower semicontinuity of `gᵢ`, no convexity of `f`, and no
`µ ≤ dL` is assumed. `F* = F(x*)` for a minimizer `x* ∈ dom g` of `F` (the non-empty solution
set). With `i₀, i₁, …` independent and uniform on the `d` coordinates, `x_k` is a function of the
history, and `E[F(x_k) − F*]` is exactly the average over all `d^k` histories. The run starts in
`dom g` (`x0 ∈ sepDom Dc`); off `dom g` the paper's right side is infinite or undefined. -/
theorem theorem_6_prox_cd_linear_rate {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {Dc : Fin d → Set ℝ} {L μ : ℝ} (hd : 0 < d) (hL : 0 < L)
    (hf : Differentiable ℝ f)
    (hsmooth : ∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2)
    (hg : ∀ i, ConvexOn ℝ (Dc i) (gc i))
    {xstar : EuclideanSpace ℝ (Fin d)} (hxD : xstar ∈ sepDom Dc)
    (hmin : ∀ z ∈ sepDom Dc, f xstar + sepG gc xstar ≤ f z + sepG gc z)
    (hPL : IsProxPL f (sepG gc) (sepDom Dc) L μ xstar)
    {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ sepDom Dc)
    {x : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d)}
    (hrun : IsProxCDRun f gc Dc L x0 x) :
    ∀ k : ℕ, 1 / (d : ℝ) ^ k * ∑ s : Fin k → Fin d,
        (f (x k s) + sepG gc (x k s) - (f xstar + sepG gc xstar)) ≤
      (1 - μ / (d * L)) ^ k * (f x0 + sepG gc x0 - (f xstar + sepG gc xstar)) := by sorry

end KarimiPL.ProxCD
