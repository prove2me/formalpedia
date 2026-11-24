-- Prove2me | Theorems.Thm_GlobalTheory_PhiPull_units_rel
-- name    : GlobalTheory.PhiPull.units_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:11.098645+00:00
-- url     : https://prove2.me/theorems/fa8923e7-ff2b-4a4c-ae5d-91f5238f802d
-- title:
--   Phi Pull: units rel
-- statement:
--   The Phi Pull construction uses the units rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L43-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {A B U : Type} [CommGroup A] [CommGroup B] [CommGroup U] {θ : B → B → B → U} {θ' : A → A → A → U}
  (β : A →* B) (Ω : A → U)
  (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a *
      Ω b * Ω c * (Ω 1)⁻¹ * θ' a b c)
include h

theorem GlobalTheory.PhiPull.units_rel (k : ℕ) (a m x : A) (g n : U) :
    Ω (x * m) ^ ((k : ℤ) - 1) * Ω (a * (x * m)) * (Ω a)⁻¹ * Ω 1 *
      (cubN θ k (β a) (β m) (β x) * (θ (β a) (β x) (β m))⁻¹ *
        ((Ω (a * m))⁻¹ * Ω a * Ω m * (Ω 1)⁻¹ * g * (Ω 1 ^ (k : ℤ) * Ω m ^ (-(k : ℤ)) * n))) =
    Ω x ^ ((k : ℤ) - 1) * Ω (a * m ^ k * x) * (Ω (a * m ^ k))⁻¹ * Ω 1 *
      (cubN θ' k a m x * (θ' a x m)⁻¹ * (g * n)) := by sorry
