-- Prove2me | Theorems.Thm_GlobalTheory_SigmaExtCount_twist_twist
-- name    : GlobalTheory.SigmaExtCount.twist_twist
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:27.0969+00:00
-- url     : https://prove2.me/theorems/17a0fcab-7f99-4fc2-b5e5-4456dc67bc97
-- title:
--   Sigma Ext Count: twist twist
-- statement:
--   The Sigma Ext Count construction uses the twist twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L220-L227

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

theorem GlobalTheory.SigmaExtCount.twist_twist (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (f : M₂ →ₗ[O] A₁ ⧸ M₁) : twist hcc σ₁ σ₂ hs₁ hs₂ (twist hcc σ₁ σ₂ hs₁ hs₂ f) = f := by sorry
