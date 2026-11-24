-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_apply_eq_zero
-- name    : GlobalTheory.CompanionTheory.SW.SchurChar.apply_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:24.468921+00:00
-- url     : https://prove2.me/theorems/2a5d6ada-418c-495a-b46e-f11cb210d209
-- title:
--   Schur Char: apply eq zero
-- statement:
--   The Schur Char construction uses the apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L77-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AdelicProofs/SchurTranslationsCharacters.lean#L77-L149

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SchurChar
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
  {χ : V → V → ℂ} {μ : Measure V}

theorem GlobalTheory.CompanionTheory.SW.SchurChar.apply_eq_zero (h : NADual V χ μ) {T : (V → ℂ) → (V → ℂ)}
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hchar : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    {φ : V → ℂ} (hφ : SB φ) {x : V} (hx : φ x = 0) : T φ x = 0 := by sorry
