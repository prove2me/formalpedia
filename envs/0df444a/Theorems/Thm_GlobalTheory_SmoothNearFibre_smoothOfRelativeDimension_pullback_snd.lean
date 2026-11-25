-- Prove2me | Theorems.Thm_GlobalTheory_SmoothNearFibre_smoothOfRelativeDimension_pullback_snd
-- name    : GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:47.444817+00:00
-- url     : https://prove2.me/theorems/1cef27b4-2cff-4ece-b2cf-f9e2f5507312
-- title:
--   Smooth Near Fibre: smooth Of Relative Dimension pullback snd
-- statement:
--   The Smooth Near Fibre construction uses the smooth Of Relative Dimension pullback snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothOfRelDimOfIsUnitProperFlat.lean#L56-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothOfRelDimOfIsUnitProperFlat.lean#L56-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothOfRelDimOfIsUnitProperFlat
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SmoothNearFibre
open GlobalTheory.VeryDenseFibres

theorem GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd {Z S T : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S) (g : ℕ)
    (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by sorry
