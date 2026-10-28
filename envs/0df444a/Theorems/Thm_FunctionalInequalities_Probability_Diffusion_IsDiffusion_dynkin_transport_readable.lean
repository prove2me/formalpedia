-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_dynkin_transport_readable
-- name    : FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:13.888062+00:00
-- url     : https://prove2.me/theorems/f6431279-4b25-42b2-b8ca-132fe14a47cf
-- title:
--   Transported Dynkin Identity in Finite Dimensions
-- statement:
--   This is Dynkin's identity in a finite-dimensional state space $V$. Let $\Phi:V\simeq\mathrm{Fin}(N)\to\mathbb R$ be a continuous linear equivalence. Assume the coordinate process $\Phi\circ Y$ is an `IsDiffusion` with transported drift and noise, while $b$ and each $\sigma_k$ on $V$ are continuous and compactly supported; also assume the stated filtration, null-set, and $C^2$ hypotheses. For every $T\ge0$, $F(Y_T)$ is integrable and
--
--   $$
--   \mathbb E[F(Y_T)]-F(x_0)
--   =\mathbb E\!\left[\int_{(0,T]}\mathcal L_{b,\sigma}F(Y_s)\,ds\right].
--   $$
--
--   The generator on the right is the coordinate-free `diffusionGenerator b σ F`; the transported coordinate generator is identified with it by `diffusionGenerator_transport_readable`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsDiffusion.dynkin_transport (Φ : V ≃L[ℝ] (Fin N → ℝ))
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       {b : V → V} {σ : V → Fin d → V} {x₀ : V}
--       (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
--       (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
--       {Y : ℝ → Ω → V}
--       (h : IsDiffusion W ℱ hW (transportDrift Φ b) (transportNoise Φ σ) (Φ x₀) (fun t ω => Φ (Y t ω)))
--       {F : V → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
--       Integrable (fun ω => F (Y T ω)) P ∧
--         ∫ ω, F (Y T ω) ∂P - F x₀ =
--           ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Transport`](https://prove2.me/theorems/d4891633-0f13-4f16-95c2-a8857d3d0e3e).
--
--   Definition modules: [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`Probability/Diffusion/Setup`](https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd).
--
--   Supporting theorems: [`IsDiffusion.dynkin`](https://prove2.me/theorems/627e15b7-06ac-4710-8cd9-58caf582f318), [`diffusionGenerator_transport`](https://prove2.me/theorems/9a1d8a25-4515-49cd-b4f2-f5f23338d6b2).
--
--   [Source excerpt, lines 43–54](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Transport.lean#L43-L54) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Transport.lean#L39-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Transport`, declaration `FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Transport

open MeasureTheory ProbabilityTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {N d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport_readable (Φ : V ≃L[ℝ] (Fin N → ℝ))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {b : V → V} {σ : V → Fin d → V} {x₀ : V}
    (hbc : Continuous b) (hσc : ∀ k, Continuous fun x => σ x k)
    (hbs : HasCompactSupport b) (hσs : ∀ k, HasCompactSupport fun x => σ x k)
    {Y : ℝ → Ω → V}
    (h : IsDiffusion W ℱ hW (transportDrift Φ b) (transportNoise Φ σ) (Φ x₀) (fun t ω => Φ (Y t ω)))
    {F : V → ℝ} (hF : ContDiff ℝ 2 F) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (Y T ω)) P ∧
      ∫ ω, F (Y T ω) ∂P - F x₀ =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, diffusionGenerator b σ F (Y s ω) ∂volume ∂P := by sorry
