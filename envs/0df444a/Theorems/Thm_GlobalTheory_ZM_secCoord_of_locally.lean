-- Prove2me | Theorems.Thm_GlobalTheory_ZM_secCoord_of_locally
-- name    : GlobalTheory.ZM.secCoord_of_locally
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:33.048569+00:00
-- url     : https://prove2.me/theorems/4a5f7c35-c09e-40f3-822b-6669fa19c84b
-- title:
--   ZM: sec Coord of locally
-- statement:
--   The ZM construction uses the sec Coord of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L87-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L87-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
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
open GlobalTheory GlobalTheory.ZM

theorem GlobalTheory.ZM.secCoord_of_locally (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R]
    (x : Sp R ⟶ X) (v : I → R) (_hM : M.IsLB) (hv : Ideal.span (Set.range v) = ⊤)
    (H : ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧
      p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) :
    SecCoord M th x v := by sorry
