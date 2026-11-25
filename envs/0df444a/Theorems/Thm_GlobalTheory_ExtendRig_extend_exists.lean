-- Prove2me | Theorems.Thm_GlobalTheory_ExtendRig_extend_exists
-- name    : GlobalTheory.ExtendRig.extend_exists
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:15.854942+00:00
-- url     : https://prove2.me/theorems/29e52ead-20d9-4828-88d1-e9d40d7925e2
-- title:
--   Extend Rig: extend exists
-- statement:
--   The Extend Rig construction uses the extend exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L65-L81

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

theorem GlobalTheory.ExtendRig.extend_exists :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B], IsRegularRing B) → (∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R], UniqueFactorizationMonoid R) → (∀ (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen) → Semi.extend_existsSt.{0} := by sorry
