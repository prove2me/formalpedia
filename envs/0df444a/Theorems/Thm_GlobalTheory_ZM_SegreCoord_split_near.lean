-- Prove2me | Theorems.Thm_GlobalTheory_ZM_SegreCoord_split_near
-- name    : GlobalTheory.ZM.SegreCoord.split_near
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:28.403426+00:00
-- url     : https://prove2.me/theorems/ba8ce048-c3b0-4d3c-954f-9d476c1beb1c
-- title:
--   Segre Coord: split near
-- statement:
--   The Segre Coord construction uses the split near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SegreCoordinates.lean#L172-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SegreCoordinates.lean#L172-L193

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
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y} {σ₁ σ₂ : Type}
  (s : σ₁ → H.Sec) (t : σ₂ → K.Sec)

theorem GlobalTheory.ZM.SegreCoord.split_near (hH : H.IsLB) (hK : K.IsLB) {T : Type} [CommRing T] (x : Sp T ⟶ P)
    (w : σ₁ × σ₂ → T) (hw : SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x w)
    (z : Sp T) : ∃ (T' : Type) (_ : CommRing T') (φ : T →+* T'), IsOpenImmersion (spMap φ) ∧
      z ∈ Set.range (spMap φ) ∧ ∃ a b, SecCoord H s (spMap φ ≫ x ≫ p) a ∧ SecCoord K t (spMap φ ≫ x ≫ q) b ∧
        ∀ i, φ (w i) = a i.1 * b i.2 := by sorry
