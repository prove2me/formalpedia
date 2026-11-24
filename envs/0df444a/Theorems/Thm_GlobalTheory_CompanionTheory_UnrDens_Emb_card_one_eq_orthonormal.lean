-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_card_one_eq_orthonormal
-- name    : GlobalTheory.CompanionTheory.UnrDens.Emb.card_one_eq_orthonormal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:38.892463+00:00
-- url     : https://prove2.me/theorems/8ddacced-bb4f-483b-8193-8b7b2e64934e
-- title:
--   Emb: card one eq orthonormal
-- statement:
--   The Emb construction uses the card one eq orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L49-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L49-L73

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

theorem GlobalTheory.CompanionTheory.UnrDens.Emb.card_one_eq_orthonormal (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) :
    Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} =
      Nat.card {x : Fin n → (Fin m → E) //
        ∀ i j, (HermSp.ofMatrix hτ S hS hd).h (x i) (x j) = if i = j then 1 else 0} := by sorry
