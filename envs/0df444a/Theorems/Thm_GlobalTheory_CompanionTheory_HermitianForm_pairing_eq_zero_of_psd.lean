-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermitianForm_pairing_eq_zero_of_psd
-- name    : GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:46.229805+00:00
-- url     : https://prove2.me/theorems/d4ca0c9b-2c2f-4528-8d9c-3acfd1ec55a0
-- title:
--   Hermitian Form: pairing eq zero of psd
-- statement:
--   The Hermitian Form construction uses the pairing eq zero of psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianPsdIsotropicRadical.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianPsdIsotropicRadical.lean#L44-L56

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianPsdIsotropicRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermitianForm

theorem GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by sorry
