-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GapOpCount_card_two_equations
-- name    : GlobalTheory.CompanionTheory.GapOpCount.card_two_equations
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:40.88806+00:00
-- url     : https://prove2.me/theorems/a459d5cc-3a62-4238-b762-fdee32edc095
-- title:
--   Gap Op Count: card two equations
-- statement:
--   The Gap Op Count construction uses the card two equations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanes.lean#L43-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanes.lean#L43-L76

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
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

theorem GlobalTheory.CompanionTheory.GapOpCount.card_two_equations (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) :
    Fintype.card k ^ 2 * (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by sorry
