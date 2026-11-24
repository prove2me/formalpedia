-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiagDom_small_perturbation_injective_pos
-- name    : GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:25.504416+00:00
-- url     : https://prove2.me/theorems/4fdfd54d-0e50-437c-8bf8-12c2a3e46a18
-- title:
--   Diag Dom: small perturbation injective pos
-- statement:
--   The Diag Dom construction uses the small perturbation injective pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NearIdentityMatrixPositiveSolution.lean#L20-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NearIdentityMatrixPositiveSolution.lean#L20-L78

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NearIdentityMatrixPositiveSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiagDom

theorem GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos :
    ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ,
      (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
      (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
      ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) →
        (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by sorry
