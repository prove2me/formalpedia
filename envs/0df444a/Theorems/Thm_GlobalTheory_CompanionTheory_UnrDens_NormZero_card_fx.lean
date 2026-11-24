-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_card_fx
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormZero.card_fx
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:53.857806+00:00
-- url     : https://prove2.me/theorems/0c86989d-930d-4868-ae7b-8fb8e347b12a
-- title:
--   Norm Zero: card fx
-- statement:
--   The Norm Zero construction uses the card fx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L27-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZero.lean#L27-L50

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

theorem GlobalTheory.CompanionTheory.UnrDens.NormZero.card_fx (h : ResAlg E τ q ε) : Nat.card (Fx τ) = q := by sorry
