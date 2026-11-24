-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_exists_congr_one
-- name    : GlobalTheory.CompanionTheory.UnrDens.exists_congr_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:46.889654+00:00
-- url     : https://prove2.me/theorems/8a4897ed-e2e8-4770-ac9a-ac2c9969ed15
-- title:
--   Unr Dens: exists congr one
-- statement:
--   The Unr Dens construction uses the exists congr one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsHermitianCongrToOne.lean#L9-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsHermitianCongrToOne.lean#L9-L60

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.exists_congr_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det →
      ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by sorry
