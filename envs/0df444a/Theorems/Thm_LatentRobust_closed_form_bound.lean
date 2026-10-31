-- Prove2me | Theorems.Thm_LatentRobust_closed_form_bound
-- name    : LatentRobust.closed_form_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:31.757314+00:00
-- url     : https://prove2.me/theorems/4602c4da-27a6-40d6-9718-042ce936269e
-- title:
--   App. A.3, p.22 — closed-form bound on $\mathrm{BR}(h^*)$ by two slab probabilities
-- statement:
--   Consider the latent Gaussian mixture model (5) with $k\ge1$, $W$ of full column rank, $\varphi$ differentiable with $\varphi'\ge c>0$ and $0<\pi<1$. Let $\Sigma=WW^\top$, $\tilde\mu=W\mu$, $q=\log\frac{1-\pi}{\pi}$, $\tilde x=\varphi^{-1}(x)$ (entrywise), and let $h^*$ be the classifier of Corollary 2.3. For the $\ell_2$ adversary of power $\varepsilon\ge0$,
--   $$
--   \begin{aligned}
--   \mathrm{BR}(h^*)\le{}&P_{x,y}\Big(\tfrac q2\le\tilde x^\top\Sigma^\dagger\tilde\mu\le\tfrac q2+\tfrac{\varepsilon}{c}\|\Sigma^\dagger\tilde\mu\|_{\ell_2},\ y=1\Big)\\
--   &+P_{x,y}\Big(\tfrac q2-\tfrac{\varepsilon}{c}\|\Sigma^\dagger\tilde\mu\|_{\ell_2}\le\tilde x^\top\Sigma^\dagger\tilde\mu\le\tfrac q2,\ y=-1\Big).
--   \end{aligned}
--   $$
--
--   The boundary risk is thereby bounded by the probability that a one-dimensional statistic falls into two thin slabs next to the threshold $q/2$.
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
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, App. A.3 (proof of Theorem 3.1), p.22, "The inner minimization in the above expression can be solved in closed form"

import Mathlib
import Definitions.Def_LatentRobust_boundaryRisk
import Definitions.Def_LatentRobust_hStar

namespace LatentRobust

/-- **Closed-form step** (Javanmard, Mehrabi, arXiv:2110.11950v2, App. A.3, p.22, "The inner minimization in the above
expression can be solved in closed form"): under the Gaussian mixture model (5) with the
standing assumptions, for the `ℓ2` adversary of power `ε ≥ 0`,
`BR(h*) ≤ P(q/2 ≤ x̃ᵀΣ†μ̃ ≤ q/2 + (ε/c)‖Σ†μ̃‖_{ℓ2}, y = 1)
  + P(q/2 − (ε/c)‖Σ†μ̃‖_{ℓ2} ≤ x̃ᵀΣ†μ̃ ≤ q/2, y = −1)`,
where `Σ = WWᵀ`, `μ̃ = Wμ`, `x̃ = φ⁻¹(x)` and `h*` is the classifier of Corollary 2.3.

**Formalization Note** The probabilities are under the joint law `gmmLaw M` of `(x, y)`;
`φ⁻¹` is `Function.invFun φ` entrywise and `†` is `pinv`. -/
theorem closed_form_bound {d k : ℕ} (M : LatentGMM d k) (c : ℝ) (hc : 0 < c)
    (hM : IsStandardGenerator M.W M.φ c) (hπ0 : 0 < M.π) (hπ1 : M.π < 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    let S := pinv (M.W * M.W.transpose)
    let μt := M.W.mulVec M.μ
    let q := logOdds M
    let ρ := fun x : Fin d → ℝ => fun i => Function.invFun M.φ (x i)
    let δ := ε / c * lpNorm 2 (S.mulVec μt)
    boundaryRisk 2 ε (gmmLaw M) (hStar M) ≤
      (gmmLaw M {xy | q / 2 ≤ ρ xy.1 ⬝ᵥ S.mulVec μt ∧ ρ xy.1 ⬝ᵥ S.mulVec μt ≤ q / 2 + δ ∧
          xy.2 = 1}).toReal +
        (gmmLaw M {xy | q / 2 - δ ≤ ρ xy.1 ⬝ᵥ S.mulVec μt ∧ ρ xy.1 ⬝ᵥ S.mulVec μt ≤ q / 2 ∧
          xy.2 = -1}).toReal := by sorry

end LatentRobust
