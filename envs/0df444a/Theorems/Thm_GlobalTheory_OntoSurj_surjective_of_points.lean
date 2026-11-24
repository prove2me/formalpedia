-- Prove2me | Theorems.Thm_GlobalTheory_OntoSurj_surjective_of_points
-- name    : GlobalTheory.OntoSurj.surjective_of_points
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:24.630694+00:00
-- url     : https://prove2.me/theorems/a29b46c7-ed43-41ce-9ace-d755b9ceeb54
-- title:
--   Onto Surj: surjective of points
-- statement:
--   The Onto Surj construction uses the surjective of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AbelianSchemeSurjectiveOfOntoComplexPoints.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AbelianSchemeSurjectiveOfOntoComplexPoints.lean#L10-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ProdSurjectiveGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AbelianSchemeSurjectiveOfOntoComplexPoints
import Theorems.Thm_GlobalTheory_GeomSurj_surjective_of_points

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

theorem GlobalTheory.OntoSurj.surjective_of_points {R K : Type} [CommRing R] [Field K] [IsAlgClosed K] (σ : R →+* K)
    (hσ : Function.Injective σ) {P A : Scheme.{0}} (a : A ⟶ Sp R) [LocallyOfFiniteType a]
    (ha : IsOpenMap a) (ψ : P ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by sorry
