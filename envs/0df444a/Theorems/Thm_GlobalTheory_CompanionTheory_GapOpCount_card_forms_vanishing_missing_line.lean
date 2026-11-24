-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_card_forms_vanishing_missing_line
-- name    : GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:46.260578+00:00
-- url     : https://prove2.me/theorems/f6f3eccd-a2e1-4b38-a115-aa8de98abdb6
-- title:
--   Gap Op Count: card forms vanishing missing line
-- statement:
--   The Gap Op Count construction uses the card forms vanishing missing line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFunctionalsVanishingSubspace.lean#L7-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFunctionalsVanishingSubspace.lean#L7-L68

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpCount

theorem GlobalTheory.CompanionTheory.GapOpCount.card_forms_vanishing_missing_line : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
    Module.finrank k M + (j + 1) = n + 1 →
    (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by sorry
