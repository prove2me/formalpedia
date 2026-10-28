-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_weighted_noise_zero_readable
-- name    : FunctionalInequalities.Probability.Diffusion.weighted_noise_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:00.117981+00:00
-- url     : https://prove2.me/theorems/8e62e3fa-0f3e-4a2a-b04e-1c9e25a67185
-- title:
--   Vanishing Weighted Noise Sum
-- statement:
--   This auxiliary statement concerns a finite family of Brownian integrands. Let $(Ω,P)$ be a probability space, let $W$ be an $N$-dimensional Brownian motion with Brownian filtration $ℱ$, and let $H_p:Ω×ℝ→ℝ$ for $p∈Fin\,N$ be jointly measurable, progressively measurable, and of finite squared `ENNReal` energy on every positive time interval. Let $c:Fin\,N→ℝ$ satisfy
--
--   $$\sum_p c(p)H_p(ω,s)=0$$
--
--   for every $ω,s$. Then, for every $T>0$,
--
--   $$\sum_p c(p)\,\texttt{stochasticIntegralBrownian}(H_p,T)=0\quad P\text{-almost everywhere}.$$
--
--    It records the consequence of pointwise cancellation of the weighted integrands and is reused in the diffusion argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem weighted_noise_zero
--       (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (hW : IsBrownianFiltration W ℱ)
--       (H : Fin N → Ω → ℝ → ℝ)
--       (hm : ∀ p, Measurable (Function.uncurry (H p)))
--       (hp : ∀ p, Probability.ProgressivelyMeasurable ℱ (H p))
--       (hq : ∀ p (T : ℝ), 0 < T →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (c : Fin N → ℝ) (hz : ∀ ω s, ∑ p, c p * H p ω s = 0)
--       {T : ℝ} (hT : 0 < T) :
--       ∀ᵐ ω ∂P, ∑ p, c p * stochasticIntegralBrownian W ℱ hW
--         (H p) (hm p) (hp p) (hq p) T ω = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Dynkin`](https://prove2.me/theorems/ee9571d4-2835-4ab8-aa76-a9be712193b7).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`exists_stochasticIntegralBrownian_finsetSum`](https://prove2.me/theorems/b0d141d4-c156-4326-80cf-9bf508518511), [`lintegral_sq_bounded_mul_lt_top`](https://prove2.me/theorems/fa63e2ae-b5b3-434d-89f7-ccbf3c60fe6e), [`stochasticIntegralBrownian_ae_zero`](https://prove2.me/theorems/57111c52-f9fc-4a29-b5e6-79796fbc45a3), [`stochasticIntegralBrownian_const_mul`](https://prove2.me/theorems/ac110cf4-8674-43ad-ab92-f7fde08971b6).
--
--   Previous: [`IsDiffusion.dynkin`](https://prove2.me/theorems/627e15b7-06ac-4710-8cd9-58caf582f318) · Next: [`IsDiffusion.ae_linear_eq_integral`](https://prove2.me/theorems/6d3adf9d-0e82-429c-930c-0f1ece93e1b1).
--
--   [Source excerpt, lines 273–284](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean#L273-L284) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean#L273-L325 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Dynkin`, declaration `_private.FunctionalInequalities.Probability.Diffusion.Dynkin.0.FunctionalInequalities.Probability.Diffusion.weighted_noise_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Dynkin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}

theorem FunctionalInequalities.Probability.Diffusion.weighted_noise_zero_readable
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : IsBrownianFiltration W ℱ)
    (H : Fin N → Ω → ℝ → ℝ)
    (hm : ∀ p, Measurable (Function.uncurry (H p)))
    (hp : ∀ p, Probability.ProgressivelyMeasurable ℱ (H p))
    (hq : ∀ p (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (c : Fin N → ℝ) (hz : ∀ ω s, ∑ p, c p * H p ω s = 0)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∑ p, c p * stochasticIntegralBrownian W ℱ hW
      (H p) (hm p) (hp p) (hq p) T ω = 0 := by sorry
