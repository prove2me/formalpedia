-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_blkEmb_mul_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.blkEmb_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:45.914011+00:00
-- url     : https://prove2.me/theorems/16ac06de-37f0-4be5-a12c-21df295695c8
-- title:
--   Conj: blk Emb mul apply
-- statement:
--   The Conj construction uses the blk Emb mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L13-L32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
variable {K : Type} [Field K]

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.blkEmb_mul_apply {d j : ℕ} (hj : j ≤ d) (A : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (blkEmb K d j A * M) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by sorry
