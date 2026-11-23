-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_avg_apply
-- name    : GlobalTheory.CompanionTheory.PRep.JacExact.avg_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:35.908944+00:00
-- url     : https://prove2.me/theorems/6ff37628-bd1b-4f40-bc1b-a0f76129a2f5
-- title:
--   Jac Exact: avg apply
-- statement:
--   The Jac Exact construction uses the avg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteSupport.lean#L17-L19

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

theorem GlobalTheory.CompanionTheory.PRep.JacExact.avg_apply (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [Fintype (L ⧸ M)] (x : V) :
    avg τ χ M x = ∑ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) x := by sorry
