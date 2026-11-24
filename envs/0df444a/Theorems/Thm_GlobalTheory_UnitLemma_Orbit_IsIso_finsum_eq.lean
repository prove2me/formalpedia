-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Orbit_IsIso_finsum_eq
-- name    : GlobalTheory.UnitLemma.Orbit.IsIso.finsum_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:22.364398+00:00
-- url     : https://prove2.me/theorems/0f7dec21-aad0-4cb1-aee9-2f8555844f35
-- title:
--   Is Iso: finsum eq
-- statement:
--   The Is Iso construction uses the finsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L352-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfIdem.lean#L352-L375

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
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}

theorem GlobalTheory.UnitLemma.Orbit.IsIso.finsum_eq (h : IsIso φ) (F : C.A → ℚ) (hF : ∀ (x : C.A) (u : C.Aˣ), F (x * (u * C.σ (u : C.A))) = F x) :
    ∑ᶠ k : C.Cl, F k.rep = ∑ᶠ k : B.Cl, F (φ k.rep) := by sorry
