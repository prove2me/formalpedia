-- Prove2me | Theorems.Thm_LatentRobust_ell2_boundary_risk_bound
-- name    : LatentRobust.ell2_boundary_risk_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:49.127739+00:00
-- url     : https://prove2.me/theorems/1a294580-d349-4fa2-8d9f-ea1b049b58f8
-- title:
--   App. A.3, p.22 — $c\sqrt{2\pi}\,\mathrm{BR}(h^*)\le\varepsilon/\sigma_{\min}(W)$ for $\ell_2$ adversaries
-- statement:
--   Consider the latent Gaussian mixture model (5) with $k\ge1$, $W$ of full column rank, $\varphi$ differentiable with $\varphi'\ge c>0$ and $0<\pi<1$, and let $h^*$ be the classifier of Corollary 2.3. For the $\ell_2$ adversary of power $\varepsilon\ge0$,
--   $$
--   c\sqrt{2\pi}\,\mathrm{BR}(h^*)\le\frac{\varepsilon}{\sigma_{\min}(W)} .
--   $$
--   The bound holds for every mean $\mu$ (including $\mu=0$) and every $d$.
--
--   Together with the comparison of $\ell_p$ and $\ell_2$ adversaries it gives Theorem 3.1.
--
--   Differences from the source:
--   - generalization: W ∈ ℝ^{d×k} tall (k < d) → any d and k with W of full column rank (no k < d); reason: no step uses k < d; the statement for every d specializes to tall W
--   - reading: latent vector z ∈ ℝ^k → 1 ≤ k; reason: the latent dimension is a positive integer; σ_min(W), the smallest nonzero singular value, does not exist for k = 0
--   - encoding: y ∼ Bern(π, {+1, −1}) with q = log((1 − π)/π) → 0 < π < 1; reason: nondegeneracy condition: q is undefined for π ∈ {0, 1}
--   - reading: sign(·) with values in {+1, −1}, ties to −1 (p.7 gives +1 when +1 has the higher likelihood, p.19 gives the negative label on {η ≤ 1/2}) → sgn t = +1 for t > 0 and −1 for t ≤ 0; reason: a {±1}-valued classifier needs a value at 0, and this is the page's tie; Real.sign would give 0
--   - encoding: φ⁻¹ applied entrywise → Function.invFun φ applied entrywise; reason: under φ' ≥ c > 0, φ is a bijection of ℝ and invFun φ is its inverse
--   - encoding: the Moore–Penrose inverse † → pinv, the matrix satisfying the four Penrose conditions (chosen by Classical.epsilon); reason: the Penrose conditions determine A† uniquely and it exists for every real matrix
--   - encoding: probabilities P_{x,y} under the Gaussian mixture model (5) → measures of the joint law gmmLaw M on ℝ^d × ℝ, the mixture π·Law(φ(W(μ+g)), +1) + (1−π)·Law(φ(W(−μ+g)), −1) with g ∼ N(0, I_k); reason: this is the law of (x, y) under (5)
--   - encoding: inf_{‖x′−x‖ ≤ ε} h(x′)y ≤ 0 in the adversarial risk (3) → ∃ x′ with ‖x′ − x‖ ≤ ε and h(x′)y ≤ 0; reason: h is {±1}-valued, so the infimum over the ball is attained
--   - encoding: the adversary's power ε_p, the radius of a ball → 0 ≤ ε; reason: a radius is nonnegative, so no instance of the source is excluded
--   - encoding: σ_min(W), the smallest nonzero singular value → the singular value of index k − 1 (zero-based, decreasing) of W acting ℝ^k → ℝ^d; reason: for W of full column rank with k ≥ 1 all k singular values are positive, so this is the smallest nonzero one
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.22, display after (19)

import Mathlib
import Definitions.Def_LatentRobust_boundaryRisk
import Definitions.Def_LatentRobust_hStar
import Definitions.Def_LatentRobust_sigmaMin

namespace LatentRobust

/-- **The `ℓ2` bound** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.22): under the Gaussian mixture model (5) with
the standing assumptions (`W` of full column rank, `k ≥ 1`, `φ' ≥ c > 0`, `π ∈ (0, 1)`), the
boundary risk of the classifier `h*` of Corollary 2.3 against the `ℓ2` adversary of power
`ε ≥ 0` satisfies `c√(2π) BR(h*) ≤ ε/σ_min(W)`.

**Formalization Note** Every `μ ∈ ℝ^k` is allowed (including `μ = 0`), and the bound is
non-asymptotic. -/
theorem ell2_boundary_risk_bound {d k : ℕ} (M : LatentGMM d k) (c : ℝ) (hc : 0 < c)
    (hM : IsStandardGenerator M.W M.φ c) (hπ0 : 0 < M.π) (hπ1 : M.π < 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    c * Real.sqrt (2 * Real.pi) * boundaryRisk 2 ε (gmmLaw M) (hStar M) ≤ ε / sigmaMin M.W := by sorry

end LatentRobust
