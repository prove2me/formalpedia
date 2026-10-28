-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_IsBorellDensity_ae_continuous_readable
-- name    : FunctionalInequalities.KLS.IsBorellDensity.ae_continuous_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:06.296444+00:00
-- url     : https://prove2.me/theorems/478771a1-189a-4be0-959d-cfd95147cfff
-- title:
--   Almost-Everywhere Continuity of Finite-Dimensional Borell Densities
-- statement:
--   This statement establishes almost-everywhere continuity for a finite-dimensional `IsBorellDensity`.
--
--   Let $V$ be a finite-dimensional real normed vector space equipped with its Borel measurable structure, let $m$ be an additive Haar measure on $V$, let $ν$ be a measure on $V$, and let $ρ : V → ℝ$ satisfy `IsBorellDensity ν m ρ`. Then
--
--   $$
--   \text{for }m\text{-almost every }x\in V,\qquad \operatorname{ContinuousAt}(ρ,x).
--   $$
--
--   This is a technical regularity result used when passing from pointwise properties of Borell densities to almost-everywhere statements.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.IsBorellDensity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_continuous {ν m : Measure V} [m.IsAddHaarMeasure]
--       {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
--       ∀ᵐ x ∂m, ContinuousAt ρ x
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548).
--
--   [Source excerpt, lines 170–172](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Basic.lean#L170-L172) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Basic.lean#L167-L187 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic`, declaration `FunctionalInequalities.KLS.IsBorellDensity.ae_continuous`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic

open MeasureTheory Set Topology Filter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.IsBorellDensity.ae_continuous_readable {ν m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    ∀ᵐ x ∂m, ContinuousAt ρ x := by sorry
