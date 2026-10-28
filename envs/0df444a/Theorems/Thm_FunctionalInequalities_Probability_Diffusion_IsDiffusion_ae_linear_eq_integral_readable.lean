-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_ae_linear_eq_integral_readable
-- name    : FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:43.625534+00:00
-- url     : https://prove2.me/theorems/6d3adf9d-0e82-429c-930c-0f1ece93e1b1
-- title:
--   Linear Functionals Annihilating Noise Follow the Drift
-- statement:
--   This statement concerns a finite-dimensional diffusion. Let $N,d∈ℕ$, let $W$ be a $d$-dimensional Brownian motion with Brownian filtration $ℱ$, and let $Y_t:Ω→ℝ^N$ be an `IsDiffusion` with continuous drift $b:ℝ^N→ℝ^N$, diffusion coefficient $σ$, and initial point $x₀$. Assume that $b$ is bounded in norm by some $B∈ℝ$. Let $ℓ:(ℝ^N)→ℝ$ be a continuous linear map satisfying
--
--   $$ℓ(σ(x,k))=0$$
--
--   for every state $x$ and noise coordinate $k$.
--
--   Then, $P$-almost surely, for every $t≥0$,
--
--   $$ℓ(Y_t)=ℓ(x₀)+\int_{(0,t]}ℓ(b(Y_s))\,ds.$$
--
--   The integral is over `Set.Ioc (0 : ℝ) t`. This is a pathwise drift identity for linear observables that annihilate every noise direction, and it is used in the localization-process analysis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 1200000 in
--   theorem IsDiffusion.ae_linear_eq_integral {W : MultidimBrownianMotion P d}
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
--       {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
--       (hbc : Continuous b) {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B)
--       {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y)
--       (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (hℓ : ∀ x k, ℓ (σ x k) = 0) :
--       ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
--         ℓ (Y t ω) = ℓ x₀ + ∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Dynkin`](https://prove2.me/theorems/ee9571d4-2835-4ab8-aa76-a9be712193b7).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`Probability/Diffusion/Setup`](https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd).
--
--   Supporting theorems: [`version_ae_eq_zero`](https://prove2.me/theorems/ee3afebe-ae0f-4c3f-aa5d-fab65a71b613), [`weighted_noise_zero`](https://prove2.me/theorems/8e62e3fa-0f3e-4a2a-b04e-1c9e25a67185).
--
--   Previous: [`weighted_noise_zero`](https://prove2.me/theorems/8e62e3fa-0f3e-4a2a-b04e-1c9e25a67185).
--
--   [Source excerpt, lines 327–335](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean#L327-L335) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean#L327-L420 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Dynkin`, declaration `FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Dynkin

open MeasureTheory ProbabilityTheory Filter Topology
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral_readable {W : MultidimBrownianMotion P d}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
    {b : (Fin N → ℝ) → Fin N → ℝ} {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {x₀ : Fin N → ℝ}
    (hbc : Continuous b) {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B)
    {Y : ℝ → Ω → Fin N → ℝ} (h : IsDiffusion W ℱ hW b σ x₀ Y)
    (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (hℓ : ∀ x k, ℓ (σ x k) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ℓ (Y t ω) = ℓ x₀ + ∫ s in Set.Ioc (0 : ℝ) t, ℓ (b (Y s ω)) := by sorry
