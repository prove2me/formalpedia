-- Prove2me | Theorems.Thm_GlobalTheory_HL_ThickSplit_cont_iUnion_cosets
-- name    : GlobalTheory.HL.ThickSplit.cont_iUnion_cosets
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:34:54.420203+00:00
-- url     : https://prove2.me/theorems/2b5c185e-92a7-48c8-90cc-ffb7aa1b0704
-- title:
--   Thick Split: cont i Union cosets
-- statement:
--   The Thick Split construction uses the cont i Union cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContentThickenedTupleOrbitNormalSubgroup.lean#L14-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContentThickenedTupleOrbitNormalSubgroup.lean#L14-L48

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroup
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ThickSplit

theorem GlobalTheory.HL.ThickSplit.cont_iUnion_cosets {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {Γ : Type} [Group Γ]
    (N H : Subgroup Γ) [N.Normal] (hN : N.index ≠ 0) (S : Γ → Set W) (c : ℝ)
    (hco : ∀ a, IsCO W0 (S a)) (hc : ∀ a, cont W0 (S a) = c)
    (heq : ∀ a b, a⁻¹ * b ∈ N ⊔ H → S a = S b)
    (hdis : ∀ a b, ¬ Disjoint (S a) (S b) → a⁻¹ * b ∈ N ⊔ H) :
    cont W0 (⋃ a, S a) * (N.relIndex H : ℝ) = (N.index : ℝ) * c := by sorry
