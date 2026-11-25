-- Prove2me | Theorems.Thm_GlobalTheory_NearFibreIso_main
-- name    : GlobalTheory.NearFibreIso.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:42.69392+00:00
-- url     : https://prove2.me/theorems/30640349-3a3c-58e6-a7f3-47d34a0e773b
-- title:
--   Near Fibre Iso: main
-- statement:
--   The Near Fibre Iso construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoFibreOfPullback.lean#L167-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoFibreOfPullback.lean#L167-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
import Theorems.Thm_GlobalTheory_DenseFibreIso_main

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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
variable (K : Type) [Field K] [Algebra R K]

theorem GlobalTheory.NearFibreIso.main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y X : Scheme.{0}) (s : X ⟶ Sp R) (φ : Y ⟶ X) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → IsProper φ → Flat (φ ≫ s) → IsIso (pullback.snd φ (pullback.fst s (spMap x))) → ∃ f : R, x f ≠ 0 ∧ IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R (Localization.Away f))))) := by sorry
