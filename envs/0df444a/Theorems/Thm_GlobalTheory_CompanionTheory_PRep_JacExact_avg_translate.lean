-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_avg_translate
-- name    : GlobalTheory.CompanionTheory.PRep.JacExact.avg_translate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:29.972665+00:00
-- url     : https://prove2.me/theorems/f13b9b56-9305-4cee-9c62-bdcd573bbc8e
-- title:
--   Jac Exact: avg translate
-- statement:
--   The Jac Exact construction uses the avg translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L21-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L21-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.PRep.JacExact.avg_translate (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [M.Normal]
    [Fintype (L ⧸ M)] (hχ : M ≤ χ.ker) (x : V) (hx : ∀ m ∈ M, τ m x = x) (n : L) :
    avg τ χ M (τ n x) = ((χ n : ℂˣ) : ℂ) • avg τ χ M x := by sorry
