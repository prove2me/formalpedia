-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_smul
-- name    : GlobalTheory.CompanionTheory.GapPolyProof.dd_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:07.560444+00:00
-- url     : https://prove2.me/theorems/136ca313-e09a-4776-9315-915f0c3620fd
-- title:
--   Gap Poly Proof: dd smul
-- statement:
--   The Gap Poly Proof construction uses the dd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L18-L19

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem GlobalTheory.CompanionTheory.GapPolyProof.dd_smul (n : ℕ) (v : ℕ → E) (a : ℂ) (ψ : E →ₗ[ℂ] ℂ) : dd n v (a • ψ) = C a * dd n v ψ := by sorry
