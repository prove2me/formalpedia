-- Prove2me | Theorems.Thm_GlobalTheory_FramePsi_hf_span_right
-- name    : GlobalTheory.FramePsi.hf_span_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:09:15.269996+00:00
-- url     : https://prove2.me/theorems/d7d19b29-6367-5443-a6d7-262009a3630e
-- title:
--   Frame Psi: hf span right
-- statement:
--   The Frame Psi construction uses the hf span right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormAdditiveCharacterTypePrimeEqOne.lean#L20-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormAdditiveCharacterTypePrimeEqOne.lean#L20-L35

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
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
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FramePsi.hf_span_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (s : Set (Fin n → E)) (hs : ∀ y ∈ s, hf L Hm x y = 0) :
    ∀ y ∈ Submodule.span E s, hf L Hm x y = 0 := by sorry
