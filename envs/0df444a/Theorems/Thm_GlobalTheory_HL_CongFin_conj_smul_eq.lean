-- Prove2me | Theorems.Thm_GlobalTheory_HL_CongFin_conj_smul_eq
-- name    : GlobalTheory.HL.CongFin.conj_smul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:31:56.264988+00:00
-- url     : https://prove2.me/theorems/33c68206-1764-5acb-917e-ce58a40cc716
-- title:
--   Cong Fin: conj smul eq
-- statement:
--   The Cong Fin construction uses the conj smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean#L85-L96

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CongFin
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}

theorem GlobalTheory.HL.CongFin.conj_smul_eq (Λ : Submodule O V) (c : E) {a : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) :
    MulAut.conj a • congSub Λ c = congSub Λ c := by sorry
