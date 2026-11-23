-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringHom_extend_of_finiteType
-- name    : GlobalTheory.exists_ringHom_extend_of_finiteType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:21.4898+00:00
-- url     : https://prove2.me/theorems/0a130977-2da1-420d-8819-5f43d0b1896a
-- title:
--   Global Theory: exists ring Hom extend of finite Type
-- statement:
--   The Global Theory construction uses the exists ring Hom extend of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SpecialisationNumberFieldAndCountableValues.lean#L16-L27

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

theorem GlobalTheory.exists_ringHom_extend_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L]
    (σ : F →+* L) : ∃ φ : A →+* L, ∀ x, φ (algebraMap F A x) = σ x := by sorry
