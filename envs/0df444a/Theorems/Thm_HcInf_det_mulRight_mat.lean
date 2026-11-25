-- Prove2me | Theorems.Thm_HcInf_det_mulRight_mat
-- name    : HcInf.det_mulRight_mat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:17.215687+00:00
-- url     : https://prove2.me/theorems/d487592c-7177-55ca-8a8d-77b6fa980b73
-- title:
--   Hc Inf: det mul Right mat
-- statement:
--   The Hc Inf construction uses the det mul Right mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean#L13-L35

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
variable {n : Type} [Fintype n] [DecidableEq n]

theorem HcInf.det_mulRight_mat (B : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulRight ℂ B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      B.det ^ Fintype.card n := by sorry
