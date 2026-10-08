-- Prove2me | Theorems.Thm_InfoGen_HighProb_theorem_4
-- name    : InfoGen.HighProb.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:09.346775+00:00
-- url     : https://prove2.me/theorems/78d58bc5-b5c5-40eb-b8ea-0544935e081e
-- title:
--   Theorem 4, p. 5 — if ℓ(w,Z) is σ-subgaussian and I(Λ_W(S);W) ≤ ε, then E|L_μ(W) − L_S(W)| ≤ √((2σ²/n)(ε + log 2))
-- statement:
--   Let $\mathsf W$ be a countable hypothesis space, $\mu$ a probability measure on $\mathsf Z$, and $\ell:\mathsf W\times\mathsf Z\to\mathbb R_+$ a jointly measurable loss such that $\ell(w,Z)$ is $\sigma$-subgaussian under $\mu$ for all $w\in\mathsf W$. Let $n\ge1$, and let $P_{W|S}$ be a learning algorithm with $I(\Lambda_{\mathsf W}(S);W)\le\varepsilon$ for some $\varepsilon\ge0$, where $\Lambda_{\mathsf W}(S) = (L_S(w))_{w\in\mathsf W}$. Then the expected absolute generalization error satisfies
--   $$\mathbb E\big|L_\mu(W) - L_S(W)\big| \le \sqrt{\frac{2\sigma^2}{n}(\varepsilon + \log 2)},$$
--   the expectation being taken under $P_{S,W} = \mu^{\otimes n}\otimes P_{W|S}$.
--
--   The paper obtains it as a byproduct of the proof of Theorem 3 with $m=1$; it improves Russo and Zou's bound $\sigma/\sqrt n + 36\sqrt{2\sigma^2\varepsilon/n}$, and with Markov's inequality gives a high-probability bound with a worse dependence on $\beta$ than Theorem 3.
--
--   **Formalization Note.** The expectation of the nonnegative quantity $|L_\mu(W) - L_S(W)|$ is a lower Lebesgue integral in $[0,\infty]$. The paper claims its results "even when $\mathsf W$ is uncountably infinite" (p. 4); under the product σ-algebra on $\mathbb R^{\mathsf W}$ this fails (for $\mathsf W = [0,1]^n$, $\ell(w,z) = \mathbf 1\{z\in\{w_1,\dots,w_n\}\}$, $\mu$ uniform on $[0,1]$ and $W = S$, one has $I(\Lambda_{\mathsf W}(S);W) = 0$ while $|L_\mu(W) - L_S(W)| = 1$), so $\mathsf W$ is countable with measurable singletons here. Joint measurability of $\ell$, $n \ge 1$ and $\varepsilon\ge0$ are added.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Theorem 4, eq. (17), p. 5 (proof: Theorem 3's proof with m = 1, App. B, p. 12)

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

namespace InfoGen.HighProb

theorem theorem_4 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε) :
    ∫⁻ p, ENNReal.ofReal |risk ℓ μ p.2 - empRisk ℓ p.1 p.2| ∂(sampleLaw μ n ⊗ₘ κ) ≤
      ENNReal.ofReal (Real.sqrt (2 * (σ : ℝ) ^ 2 / n * (ε + Real.log 2))) := by sorry

end InfoGen.HighProb
