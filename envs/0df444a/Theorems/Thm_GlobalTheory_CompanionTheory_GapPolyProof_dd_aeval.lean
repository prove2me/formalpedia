-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapPolyProof_dd_aeval
-- name    : GlobalTheory.CompanionTheory.GapPolyProof.dd_aeval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:09.229073+00:00
-- url     : https://prove2.me/theorems/95e1a6af-fc1f-435d-9a52-2aec60a42669
-- title:
--   Gap Poly Proof: dd aeval
-- statement:
--   The Gap Poly Proof construction uses the dd aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CountLeOfDvd.lean#L73-L93

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

theorem GlobalTheory.CompanionTheory.GapPolyProof.dd_aeval (S : Multiset ℂ) (n : ℕ) (hS : Multiset.card S = n + 1) (T : Module.End ℂ E) (v : ℕ → E) (x : E)
    (h0 : v 0 = x) (hn : v (n + 1) = 0)
    (hrec : ∀ j ≤ n, v (j + 1) - T (v j) = (((-1 : ℂ) ^ (j + 1)) * S.esymm (j + 1)) • x) (p : ℂ[X])
    (ψ : E →ₗ[ℂ] ℂ) :
    (S.map (fun t => X - C t)).prod ∣ p * dd n v ψ - dd n v (ψ ∘ₗ (aeval T p)) := by sorry
