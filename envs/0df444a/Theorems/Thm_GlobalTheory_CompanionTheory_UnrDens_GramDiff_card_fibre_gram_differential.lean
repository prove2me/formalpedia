-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_card_fibre_gram_differential
-- name    : GlobalTheory.CompanionTheory.UnrDens.GramDiff.card_fibre_gram_differential
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:30.693217+00:00
-- url     : https://prove2.me/theorems/249f002c-8e24-42d4-ad03-46434e02cc50
-- title:
--   Gram Diff: card fibre gram differential
-- statement:
--   The Gram Diff construction uses the card fibre gram differential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFibreGramDifferential.lean#L113-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFibreGramDifferential.lean#L113-L136

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.GramDiff
variable {E : Type} [CommRing E] (τ : E →+* E)

theorem GlobalTheory.CompanionTheory.UnrDens.GramDiff.card_fibre_gram_differential : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin m) (Fin n) E) (H : Matrix (Fin n) (Fin n) E), cT τ S = S → cT τ T = T → IsUnit T.det → cT τ x * S * x = T → cT τ H = H → Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} = q ^ (2 * m * n - n ^ 2) := by sorry
