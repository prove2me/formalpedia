-- Prove2me | Theorems.Thm_GlobalTheory_HL_CongFin_exists_pow_smul_mem
-- name    : GlobalTheory.HL.CongFin.exists_pow_smul_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:08:24.2608+00:00
-- url     : https://prove2.me/theorems/62465520-f92a-4ccd-b4fa-a76924a9f0f4
-- title:
--   Cong Fin: exists pow smul mem
-- statement:
--   The Cong Fin construction uses the exists pow smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean#L45-L54

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Theorems.Thm_GlobalTheory_PowSmulMem_exists_pow_smul_mem

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

theorem GlobalTheory.HL.CongFin.exists_pow_smul_mem {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ Λ' : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ' : Set V) = ⊤) :
    ∃ a : ℕ, ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by sorry
