-- Prove2me | Theorems.Thm_InfoGen_HighProb_eq_B_7
-- name    : InfoGen.HighProb.eq_B_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:50.686173+00:00
-- url     : https://prove2.me/theorems/e0c7bd17-7cba-4618-b00e-af3d92661bd9
-- title:
--   (B.7), p. 12 — E[max_{t∈[m]} |L_{S_t}(W_t) − L_μ(W_t)|] ≤ √((2σ²/n)(mε + log(2m))) for m parallel copies
-- statement:
--   Let $\mathsf W$ be a countable hypothesis space, $\mu$ a probability measure on $\mathsf Z$, and $\ell:\mathsf W\times\mathsf Z\to\mathbb R_+$ a jointly measurable loss such that $\ell(w,Z)$ is $\sigma$-subgaussian under $\mu$ for every $w$. Let $P_{W|S}$ be a learning algorithm with $I(\Lambda_{\mathsf W}(S);W)\le\varepsilon$, $\varepsilon\ge0$, let $n\ge1$ and $m\ge1$, and let $(S_1,W_1),\dots,(S_m,W_m)$ be $m$ independent copies of $(S,W)\sim\mu^{\otimes n}\otimes P_{W|S}$. Then
--   $$\mathbb E\Big[\max_{t\in[m]} \big|L_{S_t}(W_t) - L_\mu(W_t)\big|\Big] \le \sqrt{\frac{2\sigma^2}{n}\big(m\varepsilon + \log(2m)\big)} .$$
--
--   This is the expected-maximum bound from which Theorem 3 follows by choosing $m = \lfloor 1/\beta\rfloor$; at $m = 1$ it is Theorem 4.
--
--   **Formalization Note.** The expectation of the nonnegative maximum is a lower Lebesgue integral in $[0,\infty]$, compared with the real right-hand side through `ENNReal.ofReal`; the maximum over $[m]$ = `Fin m` is a supremum in $[0,\infty]$. In the paper (B.7) is obtained by combining (B.4) with (B.6); as printed, (B.6) bounds $\mathbb E[R^*(L_{S_{T^*}}(W^*) - L_\mu(W^*))]$, the negative of the quantity in (B.4). (B.7) is nevertheless correct (apply Lemma B.2 to the monitor that outputs $-R^*$); it is stated here as printed. $\mathsf W$ is countable with measurable singletons (see Theorem 3); joint measurability of $\ell$, $n\ge1$, $m\ge1$ and $\varepsilon\ge0$ are added.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Proof of Theorem 3, eq. (B.7), p. 12 (from (B.4) and (B.6))

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

namespace InfoGen.HighProb

theorem eq_B_7 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε) :
    ∫⁻ p, (⨆ t, ENNReal.ofReal |empRisk ℓ (p t).1 (p t).2 - risk ℓ μ (p t).2|)
        ∂(parallelLaw μ κ m) ≤
      ENNReal.ofReal (Real.sqrt (2 * (σ : ℝ) ^ 2 / n * (m * ε + Real.log (2 * m)))) := by sorry

end InfoGen.HighProb
