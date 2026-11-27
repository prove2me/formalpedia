-- Prove2me | Theorems.Thm_HcInf_cayleyLoc_of_dens
-- name    : HcInf.cayleyLoc_of_dens
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:34.558344+00:00
-- url     : https://prove2.me/theorems/7672e619-063f-5185-bbbf-5c4d4d140895
-- title:
--   Hc Inf: cayley Loc of dens
-- statement:
--   The Hc Inf construction uses the cayley Loc of dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayleyInverseMeasurable.lean#L161-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayleyInverseMeasurable.lean#L161-L162

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

theorem HcInf.cayleyLoc_of_dens (h : CayleyDens) : CayleyLoc := by sorry
