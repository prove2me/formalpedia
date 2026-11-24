-- Prove2me | Theorems.Thm_GlobalTheory_T_card_two_affine_hyperplanes
-- name    : GlobalTheory.T.card_two_affine_hyperplanes
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:27:59.000144+00:00
-- url     : https://prove2.me/theorems/e542ec8b-db38-46fe-88f6-75c019ee2516
-- title:
--   T: card two affine hyperplanes
-- statement:
--   The T construction uses the card two affine hyperplanes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanesStatement.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardTwoAffineHyperplanesStatement.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_two_affine_hyperplanes : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k), a ≠ 0 → (∀ s : k, b ≠ s • a) →
  Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by sorry
