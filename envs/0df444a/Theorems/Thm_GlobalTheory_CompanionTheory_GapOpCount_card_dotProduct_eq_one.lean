-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_card_dotProduct_eq_one
-- name    : GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:46.099932+00:00
-- url     : https://prove2.me/theorems/442d26ab-a48a-4af2-b5f0-76e793bd68c4
-- title:
--   Gap Op Count: card dot Product eq one
-- statement:
--   The Gap Op Count construction uses the card dot Product eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardAffineHyperplane.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardAffineHyperplane.lean#L7-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplane
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

theorem GlobalTheory.CompanionTheory.GapOpCount.card_dotProduct_eq_one :
    ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by sorry
