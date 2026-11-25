-- Prove2me | Theorems.Thm_GlobalTheory_mfact_mul_coeff_mvExp_linear
-- name    : GlobalTheory.mfact_mul_coeff_mvExp_linear
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:52.192799+00:00
-- url     : https://prove2.me/theorems/890f71d1-814f-4bc3-acb6-0377764b48e0
-- title:
--   Global Theory: mfact mul coeff mv Exp linear
-- statement:
--   The Global Theory construction uses the mfact mul coeff mv Exp linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MfactMulCoeffMvExpLinear.lean#L35-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MfactMulCoeffMvExpLinear.lean#L35-L60

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

theorem GlobalTheory.mfact_mul_coeff_mvExp_linear [Fintype σ] (y : σ → C) (m : σ →₀ ℕ) :
    (mfact m : C) * MvPowerSeries.coeff m (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) =
      ∏ i ∈ m.support, y i ^ m i := by sorry
