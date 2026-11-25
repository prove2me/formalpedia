-- Prove2me | Theorems.Thm_HcInf_continuousOn_cayInv
-- name    : HcInf.continuousOn_cayInv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:29.22141+00:00
-- url     : https://prove2.me/theorems/5f9c04db-fc10-5dfb-9666-68e401a6065c
-- title:
--   Hc Inf: continuous On cay Inv
-- statement:
--   The Hc Inf construction uses the continuous On cay Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PreimageSubsetImage.lean#L18-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PreimageSubsetImage.lean#L18-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PreimageSubsetImage
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

theorem HcInf.continuousOn_cayInv : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by sorry
