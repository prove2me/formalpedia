-- Prove2me | Theorems.Thm_GlobalTheory_HL_invVol_conj_of_invVol_conj
-- name    : GlobalTheory.HL.invVol_conj_of_invVol_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:37:20.870864+00:00
-- url     : https://prove2.me/theorems/c312e8ea-a50d-5d00-834e-338d6476bd3f
-- title:
--   HL: inv Vol conj of inv Vol conj
-- statement:
--   The HL construction uses the inv Vol conj of inv Vol conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InfStabilizerSmulEqConj.lean#L30-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InfStabilizerSmulEqConj.lean#L30-L54

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

theorem GlobalTheory.HL.invVol_conj_of_invVol_conj {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by sorry
