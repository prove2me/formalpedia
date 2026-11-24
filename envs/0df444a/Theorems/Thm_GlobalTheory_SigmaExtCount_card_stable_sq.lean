-- Prove2me | Theorems.Thm_GlobalTheory_SigmaExtCount_card_stable_sq
-- name    : GlobalTheory.SigmaExtCount.card_stable_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:40.250296+00:00
-- url     : https://prove2.me/theorems/1cfc937a-eaec-4814-8a0b-508056d48061
-- title:
--   Sigma Ext Count: card stable sq
-- statement:
--   The Sigma Ext Count construction uses the card stable sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L278-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L278-L311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SigmaExtCount
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

theorem GlobalTheory.SigmaExtCount.card_stable_sq (hcc : ∀ o, cO (cO o) = o) (θ : O) (hδ : IsUnit (θ - cO θ))
    (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
    (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)
    (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x)) :
    Nat.card {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ^ 2 =
    Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} := by sorry
