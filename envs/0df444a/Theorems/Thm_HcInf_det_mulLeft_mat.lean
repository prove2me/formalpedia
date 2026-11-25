-- Prove2me | Theorems.Thm_HcInf_det_mulLeft_mat
-- name    : HcInf.det_mulLeft_mat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:21:53.029463+00:00
-- url     : https://prove2.me/theorems/f950ff23-aa39-4d3b-a698-fed09eb23cda
-- title:
--   Hc Inf: det mul Left mat
-- statement:
--   The Hc Inf construction uses the det mul Left mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HuaInvOfTauDeriv.lean#L37-L48

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

theorem HcInf.det_mulLeft_mat (A : Matrix n n ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      A.det ^ Fintype.card n := by sorry
