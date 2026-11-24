-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fixed
-- name    : GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fixed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:09.325903+00:00
-- url     : https://prove2.me/theorems/fcc3d5b0-0bb0-4125-a6ec-e97c20423bd4
-- title:
--   Norm Unit: card fixed
-- statement:
--   The Norm Unit construction uses the card fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardNonzero.lean#L22-L46

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fixed (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x} = q := by sorry
