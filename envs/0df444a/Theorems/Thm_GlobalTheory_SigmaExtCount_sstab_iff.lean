-- Prove2me | Theorems.Thm_GlobalTheory_SigmaExtCount_sstab_iff
-- name    : GlobalTheory.SigmaExtCount.sstab_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:27.120861+00:00
-- url     : https://prove2.me/theorems/5e493de7-d9e7-420f-94fb-1cb8d7f6fd7b
-- title:
--   Sigma Ext Count: sstab iff
-- statement:
--   The Sigma Ext Count construction uses the sstab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L242-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardSigmaStableProdLatticeExtSq.lean#L242-L261

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

theorem GlobalTheory.SigmaExtCount.sstab_iff (hσ₂ : ∀ x, σ₂ (σ₂ x) = x) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ↔ twist hcc σ₁ σ₂ hs₁ hs₂ hM.lin = hM.lin := by sorry
