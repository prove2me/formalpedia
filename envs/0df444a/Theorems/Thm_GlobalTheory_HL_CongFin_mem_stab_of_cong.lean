-- Prove2me | Theorems.Thm_GlobalTheory_HL_CongFin_mem_stab_of_cong
-- name    : GlobalTheory.HL.CongFin.mem_stab_of_cong
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:11.028331+00:00
-- url     : https://prove2.me/theorems/ea84ec5b-9e71-4f55-a9ce-d5673b753a49
-- title:
--   Cong Fin: mem stab of cong
-- statement:
--   The Cong Fin construction uses the mem stab of cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean#L139-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean#L139-L172

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

theorem GlobalTheory.HL.CongFin.mem_stab_of_cong {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ : Set V) = ⊤) {N : ℕ} (hN : 1 ≤ N)
    (g : V ≃ₗ[E] V) (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N • w) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ := by sorry
