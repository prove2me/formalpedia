-- Prove2me | Theorems.Thm_OAI_SKGap_goe_norm_tail_s2
-- name    : OAI.SKGap.goe_norm_tail_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:09.221513+00:00
-- url     : https://prove2.me/theorems/15198bb6-0b0b-4f8b-bf35-f864d5fba22f
-- title:
--   OAI.SKGap.goe_norm_tail_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open MeasureTheory ProbabilityTheory InformationTheory Real Set`, `open scoped NNReal ENNReal`, `open Filter`, `open scoped Topology`, `open Matrix Real`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal`, `open Matrix Real`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal`, `open MeasureTheory ProbabilityTheory Real Set Filter`, `open MeasureTheory.Measure`, `open scoped ENNReal NNReal MeasureTheory Topology`, `open MeasureTheory`, `open MeasureTheory Set NormedSpace`, `open scoped Topology`, `open Matrix Real`, `open scoped BigOperators Matrix.Norms.Frobenius`, `open Set Real`, `open scoped Topology`, `open Matrix Set Filter`, `open scoped Topology Matrix.Norms.Frobenius`, `open Matrix NormedSpace ContinuousLinearMap`, `open scoped Matrix.Norms.Frobenius`, `open Matrix`, `open MeasureTheory ProbabilityTheory Real Set`, `open scoped ENNReal NNReal`, `open MeasureTheory ProbabilityTheory InformationTheory Real Set`, `open scoped NNReal ENNReal`, `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory`, `open Real`, `open scoped BigOperators Topology`, `open Filter Real`):
--
--   ```lean
--   theorem goe_norm_tail_s2 {j ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε) :
--       (gaussianCoordinates (MatrixCoordinates ι)).real
--         {g | 2*sqrt j+ε < ‖matrixOperator (goeMatrix (j/(Fintype.card ι:ℝ)) g)‖} ≤
--         2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.gaussianCoordinates`, `OAI.SKGap.goeMatrix` and `OAI.SKGap.matrixOperator` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A000

section

attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real

namespace SKGap
section GOEEvents
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem goe_norm_tail_s2 {j ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | 2*sqrt j+ε < ‖matrixOperator (goeMatrix (j/(Fintype.card ι:ℝ)) g)‖} ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j)) := by
  sorry

end GOEEvents
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end
