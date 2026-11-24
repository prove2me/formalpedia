-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_BlockEmbeddingGL_blkEmb_mul
-- name    : GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:06.529983+00:00
-- url     : https://prove2.me/theorems/69604d40-63a5-4d06-9620-f68f6bdaf6aa
-- title:
--   Block Embedding GL: blk Emb mul
-- statement:
--   The Block Embedding GL construction uses the blk Emb mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockEmbeddingGLInverse.lean#L49-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BlockEmbeddingGLInverse.lean#L49-L74

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

theorem GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul {d j : ℕ} (hjd : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) :
    blkEmb K d j (A * B) = blkEmb K d j A * blkEmb K d j B := by sorry
