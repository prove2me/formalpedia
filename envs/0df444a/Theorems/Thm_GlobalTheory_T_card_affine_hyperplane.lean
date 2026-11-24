-- Prove2me | Theorems.Thm_GlobalTheory_T_card_affine_hyperplane
-- name    : GlobalTheory.T.card_affine_hyperplane
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:47.900107+00:00
-- url     : https://prove2.me/theorems/40ace520-b050-4864-af04-955a99394702
-- title:
--   T: card affine hyperplane
-- statement:
--   The T construction uses the card affine hyperplane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardAffineHyperplaneStatement.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardAffineHyperplaneStatement.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplane
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
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

theorem GlobalTheory.T.card_affine_hyperplane : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by sorry
