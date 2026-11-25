-- Prove2me | Theorems.Thm_GlobalTheory_ZM_RepMap_exists_map_of_coord
-- name    : GlobalTheory.ZM.RepMap.exists_map_of_coord
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:08.537802+00:00
-- url     : https://prove2.me/theorems/2f07ddfd-4252-4cb6-b144-c403983a13d4
-- title:
--   Rep Map: exists map of coord
-- statement:
--   The Rep Map construction uses the exists map of coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSchemeMapOfProjectiveCoordinates.lean#L146-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSchemeMapOfProjectiveCoordinates.lean#L146-L215

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinates
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
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.ZM.RepMap.exists_map_of_coord : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by sorry
