-- Prove2me | Theorems.Thm_LatentRobust_theorem_3_1
-- name    : LatentRobust.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:39.800993+00:00
-- url     : https://prove2.me/theorems/28e83e07-c0e2-48cf-8f9a-86bfd9342e99
-- title:
--   Theorem 3.1 — the boundary risk of the Bayes-optimal classifier of the latent Gaussian mixture model vanishes as $d\to\infty$
-- statement:
--   Fix $p\ge2$ and $c>0$. For each ambient dimension $d$, let $(x,y)$ follow the latent Gaussian mixture model (5),
--   $$
--   y\sim\mathrm{Bern}(\pi_d,\{+1,-1\}),\qquad x=\varphi_d(W_dz),\qquad z\sim\mathsf N(y\mu_d,I_{k_d}),
--   $$
--   with $W_d\in\mathbb R^{d\times k_d}$, and let an $\ell_p$ adversary have power $\varepsilon_d$. Assume that for all sufficiently large $d$: $k_d\ge1$, $W_d$ has full column rank, $\varphi_d$ is differentiable with $\varphi_d'\ge c$, $0<\pi_d<1$ and $\varepsilon_d\ge0$. If
--   $$
--   \frac{\varepsilon_d\,d^{\frac12-\frac1p}}{\sigma_{\min}(W_d)}\longrightarrow0\qquad(d\to\infty),\tag{7}
--   $$
--   then the boundary risk of the Bayes-optimal classifier $h^*_d$ of Corollary 2.3 converges to zero:
--   $$
--   \mathrm{BR}(h^*_d)=\mathrm{AR}(h^*_d)-\mathrm{SR}(h^*_d)\longrightarrow0 .
--   $$
--
--   So when the latent structure is strong enough relative to the adversary's power, the Bayes-optimal classifier is asymptotically optimal for both standard and robust accuracy.
--
--   **Formalization Note** The latent dimension, weight matrix, mean, label probability, map $\varphi_d$ and adversary power may all vary with $d$ and are otherwise unrestricted.
--
--   Differences from the source:
--   - reading: letting the ambient dimension d grow to infinity, under (7) → families indexed by d ∈ ℕ (k_d, W_d, μ_d, π_d, φ_d, ε_d all depend on d; p ≥ 2 and c > 0 fixed), with the model assumptions required for all sufficiently large d; reason: the paper's asymptotic statement; requiring them at every d would be unsatisfiable at d = 0
--   - reading: dφ/dt ≥ c for some positive constant c > 0 → one constant c > 0 for all d; reason: c is a constant of the model, and (7) does not involve it
--   - encoding: ε_p d^{1/2−1/p}/σ_min(W) = o_d(1) → the sequence tends to 0; reason: equivalent for nonnegative sequences (definition of o_d, p.4)
--   - reading: the Bayes-optimal classifier → the closed form h* of Corollary 2.3 (hStar); reason: Corollary 2.3 identifies the Bayes-optimal classifier by this formula, and the proof (18) uses it
--   - generalization: W ∈ ℝ^{d×k} tall (k < d) → any d and k with W of full column rank (no k < d); reason: no step uses k < d; the statement for every d specializes to tall W
--   - reading: latent vector z ∈ ℝ^k → 1 ≤ k; reason: the latent dimension is a positive integer; σ_min(W), the smallest nonzero singular value, does not exist for k = 0
--   - encoding: y ∼ Bern(π, {+1, −1}) with q = log((1 − π)/π) → 0 < π < 1; reason: nondegeneracy condition: q is undefined for π ∈ {0, 1}
--   - reading: ‖x‖_{ℓp} = (Σ_i x_i^p)^{1/p} → (Σ_i |x_i|^p)^{1/p}; reason: the standard ℓp norm; without absolute values the expression is not a norm unless p is even
--   - reading: sign(·) with values in {+1, −1}, ties to −1 (p.7 gives +1 when +1 has the higher likelihood, p.19 gives the negative label on {η ≤ 1/2}) → sgn t = +1 for t > 0 and −1 for t ≤ 0; reason: a {±1}-valued classifier needs a value at 0, and this is the page's tie; Real.sign would give 0
--   - encoding: φ⁻¹ applied entrywise → Function.invFun φ applied entrywise; reason: under φ' ≥ c > 0, φ is a bijection of ℝ and invFun φ is its inverse
--   - encoding: the Moore–Penrose inverse † → pinv, the matrix satisfying the four Penrose conditions (chosen by Classical.epsilon); reason: the Penrose conditions determine A† uniquely and it exists for every real matrix
--   - encoding: probabilities P_{x,y} under the Gaussian mixture model (5) → measures of the joint law gmmLaw M on ℝ^d × ℝ, the mixture π·Law(φ(W(μ+g)), +1) + (1−π)·Law(φ(W(−μ+g)), −1) with g ∼ N(0, I_k); reason: this is the law of (x, y) under (5)
--   - encoding: inf_{‖x′−x‖ ≤ ε} h(x′)y ≤ 0 in the adversarial risk (3) → ∃ x′ with ‖x′ − x‖ ≤ ε and h(x′)y ≤ 0; reason: h is {±1}-valued, so the infimum over the ball is attained
--   - encoding: the adversary's power ε_p, the radius of a ball → 0 ≤ ε; reason: a radius is nonnegative, so no instance of the source is excluded
--   - encoding: σ_min(W), the smallest nonzero singular value → the singular value of index k − 1 (zero-based, decreasing) of W acting ℝ^k → ℝ^d; reason: for W of full column rank with k ≥ 1 all k singular values are positive, so this is the smallest nonzero one
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, Theorem 3.1, p.8, eq. (7) (proof A.3, pp.21–22)

import Mathlib
import Definitions.Def_LatentRobust_boundaryRisk
import Definitions.Def_LatentRobust_hStar
import Definitions.Def_LatentRobust_sigmaMin

namespace LatentRobust

open Filter Topology

/-- **Theorem 3.1** (Javanmard, Mehrabi, arXiv:2110.11950v2, §3.1, p.8): consider binary classification under the
Gaussian mixture model (5) against an adversary with `ℓp`-norm bounded power `ε_p`, `p ≥ 2`.
As the ambient dimension `d → ∞`, if the weight matrix satisfies
`ε_p d^{1/2 − 1/p} / σ_min(W) = o_d(1)` (7), then the boundary risk of the Bayes-optimal
classifier converges to zero.

**Formalization Note** `p` and `c` are fixed; for each `d` the model `M d` has its own latent
dimension `k d`, weight matrix, mean, label probability and map `φ`, and the adversary its own
power `ε d`. The standing assumptions of p.6 (`W` of full column rank, `k ≥ 1`,
`φ' ≥ c > 0`) and `π ∈ (0, 1)`, `ε ≥ 0` are required only for all sufficiently large `d`.
Condition (7) is the limit `ε_d d^{1/2 − 1/p}/σ_min(W_d) → 0`. The Bayes-optimal classifier is
the closed form `h*` of Corollary 2.3 (`hStar`), and its boundary risk is taken under the
model's joint law. -/
theorem theorem_3_1 (p c : ℝ) (hp : 2 ≤ p) (hc : 0 < c)
    (k : ℕ → ℕ) (M : ∀ d : ℕ, LatentGMM d (k d)) (ε : ℕ → ℝ)
    (hM : ∀ᶠ d in atTop, IsStandardGenerator (M d).W (M d).φ c ∧ 0 < (M d).π ∧ (M d).π < 1)
    (hε : ∀ᶠ d in atTop, 0 ≤ ε d)
    (h7 : Tendsto (fun d : ℕ => ε d * (d : ℝ) ^ ((1 : ℝ) / 2 - 1 / p) / sigmaMin (M d).W)
      atTop (𝓝 0)) :
    Tendsto (fun d : ℕ => boundaryRisk p (ε d) (gmmLaw (M d)) (hStar (M d))) atTop (𝓝 0) := by sorry

end LatentRobust
