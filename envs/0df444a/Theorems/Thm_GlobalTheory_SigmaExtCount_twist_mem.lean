-- Prove2me | Theorems.Thm_GlobalTheory_SigmaExtCount_twist_mem
-- name    : GlobalTheory.SigmaExtCount.twist_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:23.594733+00:00
-- url     : https://prove2.me/theorems/db0fd9a9-ab0c-4a02-ba21-3dbe5b4d70d5
-- title:
--   Sigma Ext Count: twist mem
-- statement:
--   The Sigma Ext Count construction uses the twist mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L229-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L229-L240

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
variable (hcc : ∀ o, cO (cO o) = o) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
  (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)

theorem GlobalTheory.SigmaExtCount.twist_mem (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x))
    {f : M₂ →ₗ[O] A₁ ⧸ M₁} (hf : f ∈ compat g₁ g₂ hg₁ hg₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f ∈ compat g₁ g₂ hg₁ hg₂ := by sorry
