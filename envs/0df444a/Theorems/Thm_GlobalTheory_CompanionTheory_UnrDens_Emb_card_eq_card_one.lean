-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_card_eq_card_one
-- name    : GlobalTheory.CompanionTheory.UnrDens.Emb.card_eq_card_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:19.468969+00:00
-- url     : https://prove2.me/theorems/104573ac-0c76-411f-8947-6f22f6456527
-- title:
--   Emb: card eq card one
-- statement:
--   The Emb construction uses the card eq card one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L21-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L21-L47

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

theorem GlobalTheory.CompanionTheory.UnrDens.Emb.card_eq_card_one {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (T g : Matrix (Fin n) (Fin n) E)
    (hg : IsUnit g.det) (hgT : cT τ g * T * g = 1) :
    Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} =
      Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} := by sorry
