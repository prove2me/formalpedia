-- Prove2me | Theorems.Thm_GlobalTheory_HL_EichlerUnip_hf_spanTo
-- name    : GlobalTheory.HL.EichlerUnip.hf_spanTo
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:56.561016+00:00
-- url     : https://prove2.me/theorems/395f7894-51b4-50a7-9ffe-4771ac4b73f6
-- title:
--   Eichler Unip: hf span To
-- statement:
--   The Eichler Unip construction uses the hf span To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerMapMemUnipotentCharacter.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EichlerMapMemUnipotentCharacter.lean#L23-L30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacter
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.EichlerUnip.hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (y : S.V)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) y = 0) {x : S.V} (hx : x ∈ S.spanTo g a) :
    hf L S.Hm x y = 0 := by sorry
