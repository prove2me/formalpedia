-- Prove2me | Theorems.Thm_HcInf_cayS_eq
-- name    : HcInf.cayS_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:21.530885+00:00
-- url     : https://prove2.me/theorems/33fd3e79-852c-479a-a5bd-7995cb74d353
-- title:
--   Hc Inf: cay S eq
-- statement:
--   The Hc Inf construction uses the cay S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExCayK.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExCayK.lean#L42-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
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

theorem HcInf.cayS_eq (hI : CayInvIff) (P Q : ℕ) (V : Set (lieU P Q)) :
    cayS V = cayS Set.univ ∩ cayInv P Q ⁻¹' V := by sorry
