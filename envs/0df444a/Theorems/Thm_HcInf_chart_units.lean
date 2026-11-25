-- Prove2me | Theorems.Thm_HcInf_chart_units
-- name    : HcInf.chart_units
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:33.856065+00:00
-- url     : https://prove2.me/theorems/077e6163-4a3c-57cc-8f78-4ccc7475dcc5
-- title:
--   Hc Inf: chart units
-- statement:
--   The Hc Inf construction uses the chart units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ContinuousAdelicGL2Det.lean#L16-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem HcInf.chart_units (G Y : Mat) (h : G * ((1 + 1) - Y) = (1 + 1) + Y) :
    (G + 1) * ((1 + 1) - Y) = (4 : ℂ) • (1 : Mat) ∧ IsUnit (G + 1).det ∧
      IsUnit ((1 + 1) - Y).det := by sorry
