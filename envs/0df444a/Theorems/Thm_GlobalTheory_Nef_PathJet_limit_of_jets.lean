-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PathJet_limit_of_jets
-- name    : GlobalTheory.Nef.PathJet.limit_of_jets
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:33.954225+00:00
-- url     : https://prove2.me/theorems/860f3210-647a-4d7d-897f-4b8ffb4d8c6a
-- title:
--   Path Jet: limit of jets
-- statement:
--   The Path Jet construction uses the limit of jets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomLimitOfDoublingJets.lean#L10-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomLimitOfDoublingJets.lean#L10-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLimitOfDoublingJets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries

theorem GlobalTheory.Nef.PathJet.limit_of_jets (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A)
    (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (φ : ℕ → A → PowerSeries R)
    (hφ : ∀ n, IsJet π ε m β δ (n + 2) (φ n))
    (hc : ∀ n f, (X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) :
    ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧
      PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧
      (PowerSeries.rescale 2).comp γ = γ.comp m := by sorry
