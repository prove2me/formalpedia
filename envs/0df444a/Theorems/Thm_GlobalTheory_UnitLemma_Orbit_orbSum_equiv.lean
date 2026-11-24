-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_orbSum_equiv
-- name    : GlobalTheory.UnitLemma.Orbit.orbSum_equiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:47.187568+00:00
-- url     : https://prove2.me/theorems/08819a9c-daac-4c17-ad84-71347d48ee03
-- title:
--   Orbit: orb Sum equiv
-- statement:
--   The Orbit construction uses the orb Sum equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L245-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L245-L295

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

theorem GlobalTheory.UnitLemma.Orbit.orbSum_equiv (φ : A ≃ₐ[O] A') (G : Subgroup Aˣ) (G' : Subgroup A'ˣ)
    (hG : ∀ t : Aˣ, t ∈ G ↔ Units.mapEquiv φ.toMulEquiv t ∈ G')
    (X : Set (Submodule O A)) (X' : Set (Submodule O A'))
    (hX : ∀ L, L ∈ X ↔ L.map φ.toLinearEquiv.toLinearMap ∈ X') :
    orbSum O G' X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by sorry
