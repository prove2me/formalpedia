-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_ReducedTopology_root_averaged_projectionShiftError_le_sat
-- name    : OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:26.422756+00:00
-- url     : https://prove2.me/theorems/e83748ad-55fe-4226-b7e2-21c19ab60dca
-- title:
--   OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le` of [lean/OAI/Probability/DilutedSpin/RootProjectionShiftError.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RootProjectionShiftError.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.ReducedTopology`, with `open _root_.MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem root_averaged_projectionShiftError_le_sat {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
--       [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
--       (a : α) (C : ι → ReducedTopology)
--       (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
--       (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
--       (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
--         DepthAverage.Regular η (fun v => Q (e j v)))
--       (T : (z : Z) → KernelTower (Ω z) L)
--       (f : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hf : ∀ z x i, |f z x i|≤1)
--       (hI : ∀ Q, Integrable (fun z => projectionShiftError a C e (T z) (f z) Q) μ) :
--       DepthAverage.average D (fun Q => ∫ z, projectionShiftError a C e (T z) (f z) Q ∂μ) ≤
--         Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
--           (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(Fintype.card ι:ℝ)^2)/(L:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.DepthAverage.Regular`, `OAI.DilutedSpinGlass.DepthAverage.average`, `OAI.DilutedSpinGlass.ReducedTopology.Admissible`, `OAI.DilutedSpinGlass.ReducedTopology.Vertex`, `OAI.DilutedSpinGlass.ReducedTopology.projectionShiftError`, `OAI.DilutedSpinGlass.ReducedTopology.vertexArity` and `OAI.DilutedSpinGlass.ReducedTopology.vertexFintype` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/RootProjectionShiftError.lean (declaration OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le)

import Mathlib
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] {L N : ℕ} [NeZero L]

theorem root_averaged_projectionShiftError_le_sat {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a}) (he : ∀ j, Function.Injective (e j))
    (η : ℝ) (hlarge : 1<η*(L:ℝ)) (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v)))
    (T : (z : Z) → KernelTower (Ω z) L)
    (f : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hf : ∀ z x i, |f z x i|≤1)
    (hI : ∀ Q, Integrable (fun z => projectionShiftError a C e (T z) (f z) Q) μ) :
    DepthAverage.average D (fun Q => ∫ z, projectionShiftError a C e (T z) (f z) Q ∂μ) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (vertexArity (C j) v:ℝ)^2))+(Fintype.card ι:ℝ)^2)/(L:ℝ)) := by
  sorry

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end
