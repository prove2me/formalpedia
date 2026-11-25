-- Prove2me | Theorems.Thm_GlobalTheory_HL_inf_stabilizer_smul_eq_conj
-- name    : GlobalTheory.HL.inf_stabilizer_smul_eq_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:37:52.013421+00:00
-- url     : https://prove2.me/theorems/1130e214-b6bb-515a-a5aa-83120feea0a2
-- title:
--   HL: inf stabilizer smul eq conj
-- statement:
--   The HL construction uses the inf stabilizer smul eq conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InfStabilizerSmulEqConj.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InfStabilizerSmulEqConj.lean#L13-L28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InfStabilizerSmulEqConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.inf_stabilizer_smul_eq_conj {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by sorry
