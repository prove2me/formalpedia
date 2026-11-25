-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_scheme_map_of_projective_coordinates
-- name    : GlobalTheory.T.exists_scheme_map_of_projective_coordinates
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:08:33.559151+00:00
-- url     : https://prove2.me/theorems/d89c6d8f-e9cc-42c3-b89f-e00d6a790b6b
-- title:
--   T: exists scheme map of projective coordinates
-- statement:
--   The T construction uses the exists scheme map of projective coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSchemeMapOfProjectiveCoordinatesStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSchemeMapOfProjectiveCoordinatesStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinatesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_scheme_map_of_projective_coordinates : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by sorry
