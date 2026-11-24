-- Prove2me | Theorems.Thm_GlobalTheory_heis_irred_of_isField
-- name    : GlobalTheory.heis_irred_of_isField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:32.610579+00:00
-- url     : https://prove2.me/theorems/420646d1-e6dd-4792-bc73-92b2993a9fc9
-- title:
--   Global Theory: heis irred of is Field
-- statement:
--   The Global Theory construction uses the heis irred of is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsFieldGlobalFnsSpec.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsFieldGlobalFnsSpec.lean#L12-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsFieldGlobalFnsSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.heis_irred_of_isField
    (H : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤)
    (R G V : Type) [CommRing R] (hR : IsField R) [CommGroup G] [Finite G] [AddCommGroup V]
    [Module R V] (hpos : 0 < Module.finrank R V) (U : G → V ≃ₗ[R] V) (e : G → G →* Rˣ)
    (h1 : ∀ x y v, U x (U y v) = (e x y : R) • U y (U x v)) (h2 : Function.Injective e)
    (h3 : Module.finrank R V ^ 2 ≤ Nat.card G) (W : Submodule R V)
    (hW : ∀ x v, v ∈ W → U x v ∈ W) : W = ⊥ ∨ W = ⊤ := by sorry
