-- Prove2me | Theorems.Thm_OAI_Kadison_CentralSpectral_scalar_indicator_commutes
-- name    : OAI.Kadison.CentralSpectral.scalar_indicator_commutes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:01:31.182099+00:00
-- url     : https://prove2.me/theorems/d9369150-e882-496d-9ca4-5f74b46d565d
-- title:
--   OAI.Kadison.CentralSpectral.scalar_indicator_commutes: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CentralSpectral`, with `open MeasureTheory Filter`, `open scoped Topology InnerProductSpace ComplexOrder`, `open CyclicSpectral Decomposable`):
--
--   ```lean
--   lemma scalar_indicator_commutes (f : C(Spectrum M,ℂ)) (s : Set (Spectrum M)) (hs : MeasurableSet s) :
--       Commute (scalarMultiplier μ f) (indicatorOperator (H:=ℂ) μ s hs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CentralCorner.center` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.CyclicSpectral.scalarMultiplier` and `OAI.Kadison.Decomposable.indicatorOperator` (definitions bundle `OAIQ039C033` of this split); `OAI.Kadison.CentralSpectral.Spectrum`, `OAI.Kadison.CentralSpectral.centerCommCStar`, `OAI.Kadison.CentralSpectral.spectrumBorel` and `OAI.Kadison.CentralSpectral.spectrumMeasurable` (definitions bundle `OAIQ039C054` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.CentralSpectral.indicator_in_scalar_spectral_range` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C054

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

variable (τ : (CentralCorner.center M) →ₚ[ℂ] ℂ)

variable (μ : Measure (Spectrum M))

variable (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] τ.GNS)

lemma scalar_indicator_commutes (f : C(Spectrum M,ℂ)) (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    Commute (scalarMultiplier μ f) (indicatorOperator (H:=ℂ) μ s hs) := by
  sorry

end Kadison.CentralSpectral

end

end
end

end OAI
end
