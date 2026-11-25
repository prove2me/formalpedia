-- Prove2me | Theorems.Thm_HcInf_cayley_set_measurable
-- name    : HcInf.cayley_set_measurable
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:39.212806+00:00
-- url     : https://prove2.me/theorems/8bae3f11-1ffd-4ccc-a504-4101944dffae
-- title:
--   Hc Inf: cayley set measurable
-- statement:
--   The Hc Inf construction uses the cayley set measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayleyInverseMeasurable.lean#L135-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayleyInverseMeasurable.lean#L135-L159

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
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

theorem HcInf.cayley_set_measurable : CaySUnivMeas := by sorry
