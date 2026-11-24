-- Prove2me | Theorems.Thm_GlobalTheory_OntoSurj_surjective_of_onto_complex_points
-- name    : GlobalTheory.OntoSurj.surjective_of_onto_complex_points
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:39.895082+00:00
-- url     : https://prove2.me/theorems/fdf5fa0e-0b7f-4297-b62f-c474a7e61093
-- title:
--   Onto Surj: surjective of onto complex points
-- statement:
--   The Onto Surj construction uses the surjective of onto complex points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AbelianSchemeSurjectiveOfOntoComplexPoints.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AbelianSchemeSurjectiveOfOntoComplexPoints.lean#L43-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ProdSurjectiveGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AbelianSchemeSurjectiveOfOntoComplexPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.OntoSurj

theorem GlobalTheory.OntoSurj.surjective_of_onto_complex_points :
    ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by sorry
