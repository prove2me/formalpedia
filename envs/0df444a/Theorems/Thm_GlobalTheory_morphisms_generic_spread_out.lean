-- Prove2me | Theorems.Thm_GlobalTheory_morphisms_generic_spread_out
-- name    : GlobalTheory.morphisms_generic_spread_out
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:55.325425+00:00
-- url     : https://prove2.me/theorems/d44f081a-8e3e-4e60-9933-4b388b822445
-- title:
--   Global Theory: morphisms generic spread out
-- statement:
--   The Global Theory construction uses the morphisms generic spread out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MorphismsGenericSpreadOut.lean#L67-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MorphismsGenericSpreadOut.lean#L67-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsGenericSpreadOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.morphisms_generic_spread_out :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B Z : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) (I : Type) [Finite I] (u : I → (pullback pB (spMap (algebraMap R K)) ⟶ Z)), QuasiCompact pB → QuasiSeparated pB → LocallyOfFinitePresentation pZ → (∀ i, u i ≫ pZ = pullback.fst _ _ ≫ pB) → ∃ (f : R) (_ : f ≠ 0) (u' : I → (pullback pB (spMap (algebraMap R (Localization.Away f))) ⟶ Z)), ∀ i, u' i ≫ pZ = pullback.fst _ _ ≫ pB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → j ≫ u' i = u i := by sorry
