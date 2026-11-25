-- Prove2me | Theorems.Thm_GlobalTheory_HL_relIndex_stabilizer_smul
-- name    : GlobalTheory.HL.relIndex_stabilizer_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:34:21.707181+00:00
-- url     : https://prove2.me/theorems/46c3bd0c-ba3b-45c6-be90-13ac280daae4
-- title:
--   HL: rel Index stabilizer smul
-- statement:
--   The HL construction uses the rel Index stabilizer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormOrbitSumLeOfSymmKernel.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormOrbitSumLeOfSymmKernel.lean#L50-L66

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)

theorem GlobalTheory.HL.relIndex_stabilizer_smul {g : G} (hg : g ∈ St) (y w : X) :
    (St ⊓ MulAction.stabilizer G (g • w)).relIndex (St ⊓ MulAction.stabilizer G (g • y)) =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by sorry
