-- Prove2me | Theorems.Thm_GlobalTheory_mvExp_eq_subst_exp
-- name    : GlobalTheory.mvExp_eq_subst_exp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:47.278244+00:00
-- url     : https://prove2.me/theorems/18c7cdf6-90c9-425e-95c6-bf7a8fd21e6d
-- title:
--   Global Theory: mv Exp eq subst exp
-- statement:
--   The Global Theory construction uses the mv Exp eq subst exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MfactMulCoeffMvExpLinear.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MfactMulCoeffMvExpLinear.lean#L18-L33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MfactMulCoeffMvExpLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory
variable {C : Type} [Field C] [CharZero C] {σ : Type}

theorem GlobalTheory.mvExp_eq_subst_exp (a : MvPowerSeries σ C) (ha : MvPowerSeries.constantCoeff a = 0) :
    mvExp a = PowerSeries.subst a (PowerSeries.exp C) := by sorry
