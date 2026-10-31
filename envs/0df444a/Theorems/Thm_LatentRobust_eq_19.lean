-- Prove2me | Theorems.Thm_LatentRobust_eq_19
-- name    : LatentRobust.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:38.000025+00:00
-- url     : https://prove2.me/theorems/71b19619-3797-4cfe-83e5-d004d37bf0cc
-- title:
--   Display (19) — $\mathrm{BR}(h^*)\le\varepsilon\|\Sigma^\dagger\tilde\mu\|/(c\sqrt{2\pi}\|\Sigma^{\dagger1/2}\tilde\mu\|)$
-- statement:
--   Consider the latent Gaussian mixture model (5) with $k\ge1$, $W$ of full column rank, $\varphi$ differentiable with $\varphi'\ge c>0$, $0<\pi<1$ and $\mu\ne0$. Let $\Sigma=WW^\top$, $\tilde\mu=W\mu$ and let $h^*$ be the classifier of Corollary 2.3. For the $\ell_2$ adversary of power $\varepsilon\ge0$,
--   $$
--   \mathrm{BR}(h^*)\le\frac{\varepsilon\,\|\Sigma^\dagger\tilde\mu\|}{c\sqrt{2\pi}\,\|\Sigma^{\dagger\,1/2}\tilde\mu\|},
--   $$
--   where $\|\cdot\|$ is the Euclidean norm and $\Sigma^{\dagger\,1/2}$ is the positive semidefinite square root of $\Sigma^\dagger$.
--
--   It is the non-asymptotic bound from which the dependence on $\sigma_{\min}(W)$ is extracted.
--
--   Differences from the source:
--   - generalization: W ∈ ℝ^{d×k} tall (k < d) → any d and k with W of full column rank (no k < d); reason: no step uses k < d; the statement for every d specializes to tall W
--   - reading: latent vector z ∈ ℝ^k → 1 ≤ k; reason: the latent dimension is a positive integer; σ_min(W), the smallest nonzero singular value, does not exist for k = 0
--   - encoding: y ∼ Bern(π, {+1, −1}) with q = log((1 − π)/π) → 0 < π < 1; reason: nondegeneracy condition: q is undefined for π ∈ {0, 1}
--   - encoding: (19), stated without a condition on μ → μ ≠ 0; reason: excludes only the case where the right side is 0/0
--   - encoding: Σ†^{1/2} → cfc Real.sqrt Σ† (continuous functional calculus of the symmetric matrix Σ†); reason: Σ† is symmetric positive semidefinite, so this is its positive semidefinite square root
--   - encoding: ‖·‖ in (19) → the Euclidean norm (lpNorm 2); reason: the same ℓ2 norm as in the preceding closed-form display
--   - reading: sign(·) with values in {+1, −1}, ties to −1 (p.7 gives +1 when +1 has the higher likelihood, p.19 gives the negative label on {η ≤ 1/2}) → sgn t = +1 for t > 0 and −1 for t ≤ 0; reason: a {±1}-valued classifier needs a value at 0, and this is the page's tie; Real.sign would give 0
--   - encoding: φ⁻¹ applied entrywise → Function.invFun φ applied entrywise; reason: under φ' ≥ c > 0, φ is a bijection of ℝ and invFun φ is its inverse
--   - encoding: the Moore–Penrose inverse † → pinv, the matrix satisfying the four Penrose conditions (chosen by Classical.epsilon); reason: the Penrose conditions determine A† uniquely and it exists for every real matrix
--   - encoding: probabilities P_{x,y} under the Gaussian mixture model (5) → measures of the joint law gmmLaw M on ℝ^d × ℝ, the mixture π·Law(φ(W(μ+g)), +1) + (1−π)·Law(φ(W(−μ+g)), −1) with g ∼ N(0, I_k); reason: this is the law of (x, y) under (5)
--   - encoding: inf_{‖x′−x‖ ≤ ε} h(x′)y ≤ 0 in the adversarial risk (3) → ∃ x′ with ‖x′ − x‖ ≤ ε and h(x′)y ≤ 0; reason: h is {±1}-valued, so the infimum over the ball is attained
--   - encoding: the adversary's power ε_p, the radius of a ball → 0 ≤ ε; reason: a radius is nonnegative, so no instance of the source is excluded
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.22, eq. (19)

import Mathlib
import Definitions.Def_LatentRobust_boundaryRisk
import Definitions.Def_LatentRobust_hStar

namespace LatentRobust

/-- **Display (19)** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.22): under the Gaussian mixture model (5) with
the standing assumptions, for the `ℓ2` adversary of power `ε ≥ 0`,
`BR(h*) ≤ ε‖Σ†μ̃‖ / (c√(2π) ‖Σ†^{1/2}μ̃‖)`, where `Σ = WWᵀ`, `μ̃ = Wμ` and `h*` is the classifier of
Corollary 2.3.

**Formalization Note** `‖·‖` is the Euclidean norm (`lpNorm 2`), `†` is `pinv` and `Σ†^{1/2}`
is the positive semidefinite square root `cfc Real.sqrt Σ†` (continuous functional calculus of
the symmetric matrix `Σ†`). The hypothesis `μ ≠ 0` excludes the case where the right side is
`0/0`. -/
theorem eq_19 {d k : ℕ} (M : LatentGMM d k) (c : ℝ) (hc : 0 < c)
    (hM : IsStandardGenerator M.W M.φ c) (hπ0 : 0 < M.π) (hπ1 : M.π < 1) (hμ : M.μ ≠ 0)
    (ε : ℝ) (hε : 0 ≤ ε) :
    boundaryRisk 2 ε (gmmLaw M) (hStar M) ≤
      ε * lpNorm 2 ((pinv (M.W * M.W.transpose)).mulVec (M.W.mulVec M.μ)) /
        (c * Real.sqrt (2 * Real.pi) *
          lpNorm 2 ((cfc Real.sqrt (pinv (M.W * M.W.transpose))).mulVec (M.W.mulVec M.μ))) := by sorry

end LatentRobust
