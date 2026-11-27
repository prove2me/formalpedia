-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_isAlgebraic_of_finiteType
-- name    : GlobalTheory.exists_algHom_isAlgebraic_of_finiteType
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:05.575727+00:00
-- url     : https://prove2.me/theorems/3ac5ee64-9927-5b8e-83c8-a3d67f89bf61
-- title:
--   Global Theory: exists alg Hom is Algebraic of finite Type
-- statement:
--   The Global Theory construction uses the exists alg Hom is Algebraic of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L6-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_algHom_isAlgebraic_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L] [Algebra F L] :
    ∃ φ : A →ₐ[F] L, ∀ x, IsAlgebraic F (φ x) := by sorry
