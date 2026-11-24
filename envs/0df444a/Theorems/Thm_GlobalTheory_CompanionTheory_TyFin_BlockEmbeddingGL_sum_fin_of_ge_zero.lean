-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_sum_fin_of_ge_zero
-- name    : GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:40.041485+00:00
-- url     : https://prove2.me/theorems/b369ac2a-2251-4be5-9cc4-9b1f74a350a6
-- title:
--   Block Embedding GL: sum fin of ge zero
-- statement:
--   The Block Embedding GL construction uses the sum fin of ge zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockEmbeddingGLInverse.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockEmbeddingGLInverse.lean#L13-L21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
variable (K : Type) [Field K]

theorem GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero {d j : ℕ} (hjd : j ≤ d) (f : Fin d → K)
    (hf : ∀ k : Fin d, j ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin j, f (Fin.castLE hjd k) := by sorry
