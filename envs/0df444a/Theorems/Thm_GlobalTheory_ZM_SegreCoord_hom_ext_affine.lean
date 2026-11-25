-- Prove2me | Theorems.Thm_GlobalTheory_ZM_SegreCoord_hom_ext_affine
-- name    : GlobalTheory.ZM.SegreCoord.hom_ext_affine
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:29.865797+00:00
-- url     : https://prove2.me/theorems/412aaaea-1340-453a-b46f-f9e9c77ed190
-- title:
--   Segre Coord: hom ext affine
-- statement:
--   The Segre Coord construction uses the hom ext affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SegreCoordinates.lean#L110-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SegreCoordinates.lean#L110-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SegreCoordinates
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SegreCoord
open GlobalTheory.ZM.RepBC GlobalTheory.AbLaw.Segre
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec}

theorem GlobalTheory.ZM.SegreCoord.hom_ext_affine {W Z : Scheme.{0}} {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂]
    (a : W ⟶ Sp T₁) (b : W ⟶ Sp T₂) (f : Sp T₁ ⟶ Z) (g : Sp T₂ ⟶ Z)
    (h : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ W) (φ₁ : T₁ →+* T) (φ₂ : T₂ →+* T), y ≫ a = spMap φ₁ →
      y ≫ b = spMap φ₂ → spMap φ₁ ≫ f = spMap φ₂ ≫ g) : a ≫ f = b ≫ g := by sorry
