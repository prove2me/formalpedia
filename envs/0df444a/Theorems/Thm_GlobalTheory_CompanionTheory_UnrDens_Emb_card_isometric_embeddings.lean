-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_card_isometric_embeddings
-- name    : GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:17.561658+00:00
-- url     : https://prove2.me/theorems/bae975d8-737a-4571-9317-d9bde0f58c8e
-- title:
--   Emb: card isometric embeddings
-- statement:
--   The Emb construction uses the card isometric embeddings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L97-L111

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Emb
variable {E : Type} [CommRing E] {τ : E →+* E}

theorem GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ),
    ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E)
    (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det →
    (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) =
      (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by sorry
