-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermitianForm_re_pairing_eq_zero_of_psd
-- name    : GlobalTheory.CompanionTheory.HermitianForm.re_pairing_eq_zero_of_psd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:39.703948+00:00
-- url     : https://prove2.me/theorems/c0453dfa-9ed4-44e8-8181-1e9da7521cf6
-- title:
--   Hermitian Form: re pairing eq zero of psd
-- statement:
--   The Hermitian Form construction uses the re pairing eq zero of psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianPsdIsotropicRadical.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianPsdIsotropicRadical.lean#L5-L42

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

theorem GlobalTheory.CompanionTheory.HermitianForm.re_pairing_eq_zero_of_psd {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by sorry
