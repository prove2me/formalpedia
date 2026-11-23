-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_Top_locE_exists_coords
-- name    : GlobalTheory.SgLoc.Top.locE_exists_coords
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:25.312215+00:00
-- url     : https://prove2.me/theorems/1ddc2fdf-8775-4621-8926-b341e98c85bc
-- title:
--   Top: loc E exists coords
-- statement:
--   The Top construction uses the loc E exists coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L96-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L96-L158

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.SgLoc.Top.locE_exists_coords [CharZero F] (L : LocE F E) :
    ∃ (ψ : (F × F) ≃ₗ[F] E) (D : F), D ≠ 0 ∧
      (∀ p : F × F, p.1 ∈ 𝒪[F] → p.2 ∈ 𝒪[F] → ψ p ∈ L.O) ∧
      (∀ p : F × F, ψ p ∈ L.O → 2 * p.1 ∈ 𝒪[F] ∧ 2 * D * p.2 ∈ 𝒪[F]) := by sorry
