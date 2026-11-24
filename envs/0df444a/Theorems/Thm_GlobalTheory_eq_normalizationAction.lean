-- Prove2me | Theorems.Thm_GlobalTheory_eq_normalizationAction
-- name    : GlobalTheory.eq_normalizationAction
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:18:14.935075+00:00
-- url     : https://prove2.me/theorems/9e081169-c451-4bb7-bc96-a70b4a118df0
-- title:
--   Global Theory: eq normalization Action
-- statement:
--   The Global Theory construction uses the eq normalization Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L744-L748
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L744-L748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
variable {G : Type v} [Group G] {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable (ρ : G →* Aut X) (σ : G →* Aut Y) (H : ∀ g, (ρ g).hom ≫ f = f ≫ (σ g).hom)

theorem GlobalTheory.eq_normalizationAction (τ : G →* Aut f.normalization)
    (h₁ : ∀ g, f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization)
    (h₂ : ∀ g, (τ g).hom ≫ f.fromNormalization = f.fromNormalization ≫ (σ g).hom) :
    τ = normalizationAction f ρ σ H := by sorry
