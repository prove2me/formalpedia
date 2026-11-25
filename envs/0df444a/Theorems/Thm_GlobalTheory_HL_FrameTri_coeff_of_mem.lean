-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameTri_coeff_of_mem
-- name    : GlobalTheory.HL.FrameTri.coeff_of_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:34:49.766599+00:00
-- url     : https://prove2.me/theorems/5b3b98db-a2a7-488d-a2ca-6ac43de80d86
-- title:
--   Frame Tri: coeff of mem
-- statement:
--   The Frame Tri construction uses the coeff of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameUnipotentUnitriangular.lean#L47-L64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTri
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.FrameTri.coeff_of_mem (g : Fin (r + 1) → S.V) {j : ℕ} {v : S.V} (hv : v ∈ S.spanTo g j) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), j ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by sorry
