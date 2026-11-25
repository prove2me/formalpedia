-- Prove2me | Theorems.Thm_GlobalTheory_T_isProjectiveCoordinateRepresentation_closedSubscheme
-- name    : GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:57.012975+00:00
-- url     : https://prove2.me/theorems/af665c34-9e7c-4911-8a8f-d82efbacd754
-- title:
--   T: is Projective Coordinate Representation closed Subscheme
-- statement:
--   The T construction uses the is Projective Coordinate Representation closed Subscheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProjectiveCoordinateRepresentationClosedSubschStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProjectiveCoordinateRepresentationClosedSubschStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubschStatement
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

theorem GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : Y ⟶ Z) (N : LB Y) (ty : σ → N.Sec), ProjRep I s M th → IsClosedImmersion i → N.IsLB → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ i) v) → ProjRep (idealOf (i ≫ s) N ty (𝟙 Y)) (i ≫ s) N ty := by sorry
