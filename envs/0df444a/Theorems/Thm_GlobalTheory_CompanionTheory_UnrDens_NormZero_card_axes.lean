-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_axes
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormZero.card_axes
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:44.885149+00:00
-- url     : https://prove2.me/theorems/382fb584-7656-480f-aa62-9fd298d9ca2a
-- title:
--   Norm Zero: card axes
-- statement:
--   The Norm Zero construction uses the card axes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L89-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L89-L109

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.UnrDens.NormZero.card_axes {F : Type} [Finite F] (z : F) :
    Nat.card {p : F × F // p.1 = z ∨ p.2 = z} + 1 = 2 * Nat.card F := by sorry
