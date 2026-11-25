-- Prove2me | Theorems.Thm_GlobalTheory_ZM_SegreCoord_secCoord_box
-- name    : GlobalTheory.ZM.SegreCoord.secCoord_box
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:00:56.562859+00:00
-- url     : https://prove2.me/theorems/6191c270-0312-5564-9136-9e054f04d0b8
-- title:
--   Segre Coord: sec Coord box
-- statement:
--   The Segre Coord construction uses the sec Coord box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SegreCoordinates.lean#L40-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SegreCoordinates.lean#L40-L69

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
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem GlobalTheory.ZM.SegreCoord.secCoord_box {σ₁ σ₂ : Type} (s : σ₁ → H.Sec) (t : σ₂ → K.Sec) {T : Type} [CommRing T] (x : Sp T ⟶ P)
    (v₁ : σ₁ → T) (v₂ : σ₂ → T) (h₁ : SecCoord H s (x ≫ p) v₁) (h₂ : SecCoord K t (x ≫ q) v₂) :
    SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x (fun i => v₁ i.1 * v₂ i.2) := by sorry
