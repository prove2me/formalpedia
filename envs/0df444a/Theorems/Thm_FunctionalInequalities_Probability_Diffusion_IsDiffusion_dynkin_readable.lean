-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_dynkin_readable
-- name    : FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:20.770997+00:00
-- url     : https://prove2.me/theorems/627e15b7-06ac-4710-8cd9-58caf582f318
-- title:
--   Dynkin Identity for Compactly Supported Diffusions
-- statement:
--   This formalizes the Dynkin identity associated with the diffusion generator. Let $Y$ be an `IsDiffusion` in $\mathbb R^N$ with drift $b$ and noise columns $\sigma_k$. Assume $b$ and each $\sigma_k$ are continuous and compactly supported, the filtration satisfies the stated pre-zero and null-set conditions, and $F:\mathbb R^N\to\mathbb R$ is $C^2$. For every $T\ge0$, $F(Y_T)$ is integrable and
--
--   $$
--   \mathbb E[F(Y_T)]-F(x_0)
--   =\mathbb E\!\left[\int_{(0,T]}\mathcal L F(Y_s)\,ds\right],
--   $$
--
--   where $\mathcal L$ is `diffusionGenerator b σ F`. This is the generator-form expectation identity used in the diffusion formalization.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsDiffusion.dynkin {W : MultidimBrownianMotion P d}
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
--       (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
--       (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
--       {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y)
--       {F : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
--       Integrable (fun ω => F (Y T ω)) P ∧
--         ∫ ω, F (Y T ω) ∂P - F x₀ =
--           ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Dynkin`](https://prove2.me/theorems/ee9571d4-2835-4ab8-aa76-a9be712193b7).
--
--   Definition modules: [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`Probability/Diffusion/Setup`](https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd).
--
--   Supporting theorems: [`IsVectorItoVersion.itoFormula_localise`](https://prove2.me/theorems/2fb489df-09de-4dc9-af35-c8013b4a86e5), [`itoFormula_of_unbounded_coeff`](https://prove2.me/theorems/26b3bb9f-845f-407e-8e95-6d9fce1413b9), [`version_ae_eq_zero`](https://prove2.me/theorems/ee3afebe-ae0f-4c3f-aa5d-fab65a71b613).
--
--   Next: [`weighted_noise_zero`](https://prove2.me/theorems/8e62e3fa-0f3e-4a2a-b04e-1c9e25a67185).
--
--   [Source excerpt, lines 97–108](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean#L97-L108) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean#L94-L271 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Dynkin`, declaration `FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Dynkin

open MeasureTheory ProbabilityTheory Filter Topology
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
set_option maxHeartbeats 1600000

theorem FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_readable {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
    (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
    (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
    {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y)
    {F : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (Y T ω)) P ∧
      ∫ ω, F (Y T ω) ∂P - F x₀ =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by sorry
