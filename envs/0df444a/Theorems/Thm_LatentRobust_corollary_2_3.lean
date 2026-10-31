-- Prove2me | Theorems.Thm_LatentRobust_corollary_2_3
-- name    : LatentRobust.corollary_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:48.287182+00:00
-- url     : https://prove2.me/theorems/0811285f-711b-4c7a-b9a2-8f57cc11c97d
-- title:
--   Corollary 2.3 — closed-form Bayes-optimal classifiers of the latent Gaussian mixture and generalized linear models
-- statement:
--   Fix $c>0$. Both clauses assume the standing assumptions on the generator $x=\varphi(Wz)$: $k\ge1$, $W\in\mathbb R^{d\times k}$ of full column rank, and $\varphi$ differentiable with $\varphi'\ge c$.
--
--   1. **Gaussian mixture model (5).** If $0<\pi<1$ and $q=\log\frac{1-\pi}{\pi}$, the classifier
--   $$
--   h^*(x)=\operatorname{sign}\Big(\varphi^{-1}(x)^\top (WW^\top)^\dagger W\mu-\frac q2\Big)
--   $$
--   satisfies $\mathrm{SR}(h^*)\le\mathrm{SR}(h)$ for every Borel classifier $h:\mathbb R^d\to\{+1,-1\}$.
--   2. **Generalized linear model (6).** If $f:\mathbb R\to[0,1]$ is nondecreasing, the classifier
--   $$
--   h^*(x)=\operatorname{sign}\Big(f\big(\beta^\top(W^\top W)^{-1}W^\top\varphi^{-1}(x)\big)-\frac12\Big)
--   $$
--   satisfies $\mathrm{SR}(h^*)\le\mathrm{SR}(h)$ for every Borel classifier $h:\mathbb R^d\to\{+1,-1\}$.
--
--   The standard risks are taken under the model's joint law of $(x,y)$. The first formula is the classifier whose boundary risk Theorem 3.1 controls.
--
--   Differences from the source:
--   - reading: the Bayes-optimal classifier can be formulated by h* / is given by h* → SR(h*) ≤ SR(h) for every Borel {±1}-valued classifier h, under the model's joint law; reason: Bayes-optimal means least standard risk among Borel classifiers (Proposition 2.2)
--   - generalization: W ∈ ℝ^{d×k} tall (k < d) → any d and k with W of full column rank (no k < d); reason: no step uses k < d; the statement for every d specializes to tall W
--   - reading: latent vector z ∈ ℝ^k → 1 ≤ k; reason: the latent dimension is a positive integer; σ_min(W), the smallest nonzero singular value, does not exist for k = 0
--   - encoding: y ∼ Bern(π, {+1, −1}) with q = log((1 − π)/π) → 0 < π < 1; reason: nondegeneracy condition: q is undefined for π ∈ {0, 1}
--   - generalization: f an increasing link function → f monotone (nondecreasing); reason: every increasing f is monotone, so the statement specializes to the source's
--   - reading: sign(·) with values in {+1, −1}, ties to −1 (p.7 gives +1 when +1 has the higher likelihood, p.19 gives the negative label on {η ≤ 1/2}) → sgn t = +1 for t > 0 and −1 for t ≤ 0; reason: a {±1}-valued classifier needs a value at 0, and this is the page's tie; Real.sign would give 0
--   - encoding: φ⁻¹ applied entrywise → Function.invFun φ applied entrywise; reason: under φ' ≥ c > 0, φ is a bijection of ℝ and invFun φ is its inverse
--   - encoding: the Moore–Penrose inverse † → pinv, the matrix satisfying the four Penrose conditions (chosen by Classical.epsilon); reason: the Penrose conditions determine A† uniquely and it exists for every real matrix
--   - encoding: (WᵀW)⁻¹ → Mathlib's matrix inverse; reason: WᵀW is invertible for W of full column rank, so this is the genuine inverse
--   - encoding: models (5) and (6) → the joint laws gmmLaw and glmLaw on ℝ^d × ℝ; reason: these are the laws of (x, y) under (5) and (6)
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, Corollary 2.3, p.7 (proof A.2, pp.19–20)

import Mathlib
import Definitions.Def_LatentRobust_boundaryRisk
import Definitions.Def_LatentRobust_hStar
import Definitions.Def_LatentRobust_hStarGLM

namespace LatentRobust

/-- **Corollary 2.3** (Javanmard, Mehrabi, arXiv:2110.11950v2, §2.3, p.7), both clauses.

1. Under the Gaussian mixture model (5), the classifier
   `h*(x) = sign(φ⁻¹(x)ᵀ (WWᵀ)† Wμ − q/2)`, `q = log((1 − π)/π)`, has standard risk at most that
   of every Borel classifier `h : ℝ^d → {+1, −1}` (it is Bayes-optimal).
2. Under the generalized linear model (6), the classifier
   `h*(x) = sign(f(βᵀ(WᵀW)⁻¹Wᵀφ⁻¹(x)) − 1/2)` has standard risk at most that of every Borel
   classifier `h : ℝ^d → {+1, −1}`.

Both models carry the standing assumptions of p.6: `W` of full column rank (`k ≥ 1`), `φ`
differentiable with `φ' ≥ c > 0`; for (5) `π ∈ (0, 1)`; for (6) `f : ℝ → [0, 1]`
nondecreasing.

**Formalization Note** "The Bayes-optimal classifier can be formulated by h*" is read as: the
displayed formula attains the least standard risk among Borel `{±1}`-valued classifiers
(Proposition 2.2). The standard risk is computed under the model's joint law (`gmmLaw`,
`glmLaw`). -/
theorem corollary_2_3 {d k : ℕ} (c : ℝ) (hc : 0 < c) :
    (∀ M : LatentGMM d k, IsStandardGenerator M.W M.φ c → 0 < M.π → M.π < 1 →
      ∀ h : (Fin d → ℝ) → ℝ, Measurable h → (∀ x, h x = 1 ∨ h x = -1) →
        standardRisk (gmmLaw M) (hStar M) ≤ standardRisk (gmmLaw M) h) ∧
    (∀ N : LatentGLM d k, IsStandardGenerator N.W N.φ c → Monotone N.f →
      (∀ t, 0 ≤ N.f t ∧ N.f t ≤ 1) →
      ∀ h : (Fin d → ℝ) → ℝ, Measurable h → (∀ x, h x = 1 ∨ h x = -1) →
        standardRisk (glmLaw N) (hStarGLM N) ≤ standardRisk (glmLaw N) h) := by sorry

end LatentRobust
