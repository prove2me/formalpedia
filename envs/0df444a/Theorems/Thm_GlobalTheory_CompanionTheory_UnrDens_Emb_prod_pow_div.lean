-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_prod_pow_div
-- name    : GlobalTheory.CompanionTheory.UnrDens.Emb.prod_pow_div
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:38.377575+00:00
-- url     : https://prove2.me/theorems/a3ef6c44-5928-4360-ae68-e7c5aa7c9608
-- title:
--   Emb: prod pow div
-- statement:
--   The Emb construction uses the prod pow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L75-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianRepresentationsResidue.lean#L75-L95

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

theorem GlobalTheory.CompanionTheory.UnrDens.Emb.prod_pow_div (x : ℝ) (hx : x ≠ 0) (n : ℕ) : ∀ m : ℕ, n ≤ m →
    ∏ i : Fin n, (x ^ (2 * (m - (i : ℕ))) / x) = x ^ (2 * m * n - n ^ 2) := by sorry
