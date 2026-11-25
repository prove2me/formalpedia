-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_isField_or_split
-- name    : GlobalTheory.SgLoc.isField_or_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:40.118187+00:00
-- url     : https://prove2.me/theorems/a9d3d8e4-95e3-52f5-8fe8-e67a7131916f
-- title:
--   Sg Loc: is Field or split
-- statement:
--   The Sg Loc construction uses the is Field or split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralValIntegerIff.lean#L91-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralValIntegerIff.lean#L91-L103

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc

theorem GlobalTheory.SgLoc.isField_or_split : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → IsField E ∨ ∃ e : E ≃ₐ[F] F × F, (∀ x, e (M.L.cj x) = (e x).swap) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x, x ∈ M.L.O ↔ ((e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) := by sorry
