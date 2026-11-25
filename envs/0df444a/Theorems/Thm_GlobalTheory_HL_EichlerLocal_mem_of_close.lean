-- Prove2me | Theorems.Thm_GlobalTheory_HL_EichlerLocal_mem_of_close
-- name    : GlobalTheory.HL.EichlerLocal.mem_of_close
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:45.534949+00:00
-- url     : https://prove2.me/theorems/2b9066be-c7c8-4393-bc8a-2a652e592b44
-- title:
--   Eichler Local: mem of close
-- statement:
--   The Eichler Local construction uses the mem of close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerLatticeLocallyConstantData.lean#L24-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerLatticeLocallyConstantData.lean#L24-L63

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerLocal
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.HL.EichlerLocal.mem_of_close (hH : IsHerm L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    {p : E} (hp : p ∈ L.O) (hpc : L.cj p = p) {x u a b : Fin n → E} {s t : E}
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u)
    (hxΛ : p • x ∈ Λ) (huΛ : u ∈ Λ) (hsO : s ∈ L.O) (ha : a ∈ Λ) (hb : b ∈ Λ) (ht : t ∈ L.O)
    {v : Fin n → E} (hv : eich L Hm x u s v ∈ Λ) :
    eich L Hm (x + p ^ 4 • a) (u + p ^ 4 • b) (s + p ^ 4 * t) v ∈ Λ := by sorry
