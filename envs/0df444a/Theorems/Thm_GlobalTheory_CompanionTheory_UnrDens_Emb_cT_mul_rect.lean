-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_cT_mul_rect
-- name    : GlobalTheory.CompanionTheory.UnrDens.Emb.cT_mul_rect
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:07.803826+00:00
-- url     : https://prove2.me/theorems/8e4260d7-d4b7-40bc-93d2-3b108c626225
-- title:
--   Emb: c T mul rect
-- statement:
--   The Emb construction uses the c T mul rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L12-L15

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

theorem GlobalTheory.CompanionTheory.UnrDens.Emb.cT_mul_rect {a b c : ℕ} (x : Matrix (Fin a) (Fin b) E) (y : Matrix (Fin b) (Fin c) E) :
    cT τ (x * y) = cT τ y * cT τ x := by sorry
