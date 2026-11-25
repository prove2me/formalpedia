-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_mem_perp_span
-- name    : GlobalTheory.HL.Inhab.mem_perp_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:38:52.966103+00:00
-- url     : https://prove2.me/theorems/f2be70e7-d2da-4637-9c3d-e279b45a05a4
-- title:
--   Inhab: mem perp span
-- statement:
--   The Inhab construction uses the mem perp span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L33-L45

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.Inhab.mem_perp_span (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (s : Set (Fin n → E))
    (x : Fin n → E) : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ s, hf L H x y = 0 := by sorry
