-- Prove2me | Theorems.Thm_GlobalTheory_ProperFlatNearFibre_exists_opens_smoothOfRelativeDimension_of_flat
-- name    : GlobalTheory.ProperFlatNearFibre.exists_opens_smoothOfRelativeDimension_of_flat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:45:35.898257+00:00
-- url     : https://prove2.me/theorems/17cd4261-b156-49fa-99b2-fd08eeae4ed4
-- title:
--   Proper Flat Near Fibre: exists opens smooth Of Relative Dimension of flat
-- statement:
--   The Proper Flat Near Fibre construction uses the exists opens smooth Of Relative Dimension of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsOpensSmoothOfRelativeDimensionOfFlat.lean#L17-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsOpensSmoothOfRelativeDimensionOfFlat.lean#L17-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsOpensSmoothOfRelativeDimensionOfFlat
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.ProperFlatNearFibre

theorem GlobalTheory.ProperFlatNearFibre.exists_opens_smoothOfRelativeDimension_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by sorry
