-- Prove2me | Theorems.Thm_GlobalTheory_ProperFlatNearFibre_smoothOfRelativeDimension_pullback_snd
-- name    : GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:46:48.914611+00:00
-- url     : https://prove2.me/theorems/d7e2a1fd-9466-4bb1-8152-21f5fb0dbf45
-- title:
--   Proper Flat Near Fibre: smooth Of Relative Dimension pullback snd
-- statement:
--   The Proper Flat Near Fibre construction uses the smooth Of Relative Dimension pullback snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsOpensSmoothOfRelativeDimensionOfFlat.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsOpensSmoothOfRelativeDimensionOfFlat.lean#L44-L63

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

theorem GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by sorry
