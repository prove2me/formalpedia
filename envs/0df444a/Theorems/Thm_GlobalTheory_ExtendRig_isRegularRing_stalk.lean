-- Prove2me | Theorems.Thm_GlobalTheory_ExtendRig_isRegularRing_stalk
-- name    : GlobalTheory.ExtendRig.isRegularRing_stalk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:18.599306+00:00
-- url     : https://prove2.me/theorems/ca8fe2c9-0dd4-4633-806a-f92ff93eedc3
-- title:
--   Extend Rig: is Regular Ring stalk
-- statement:
--   The Extend Rig construction uses the is Regular Ring stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L47-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtendRig

theorem GlobalTheory.ExtendRig.isRegularRing_stalk
    (hreg : ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B]
      [Algebra.Smooth V B], IsRegularRing B)
    (V : Type) [CommRing V] [IsRegularRing V] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V))
    [Smooth f] (x : X) : IsRegularRing (X.presheaf.stalk x) := by sorry
