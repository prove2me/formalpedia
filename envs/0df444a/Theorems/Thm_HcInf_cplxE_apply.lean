-- Prove2me | Theorems.Thm_HcInf_cplxE_apply
-- name    : HcInf.cplxE_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:21.082609+00:00
-- url     : https://prove2.me/theorems/29ad24f1-d378-54fa-b3d7-83b0eb26ced5
-- title:
--   Hc Inf: cplx E apply
-- statement:
--   The Hc Inf construction uses the cplx E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean#L155-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean#L155-L155

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HuaInvOfTauDeriv
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
open HcS.BasicNotions Matrix
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem HcInf.cplxE_apply (p : lieU P Q × lieU P Q) : cplxE p = cplx p := by sorry
