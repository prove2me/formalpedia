-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_conj_apply_lt
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.conj_apply_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:33.387457+00:00
-- url     : https://prove2.me/theorems/2ddaf216-02af-4f02-aac7-2382e43d4e97
-- title:
--   Conj: conj apply lt
-- statement:
--   The Conj construction uses the conj apply lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L61-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L61-L94

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.conj_apply_lt {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) (hAB : A * B = 1)
    (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ i l : Fin d, (l : ℕ) < j → M i l = if i = l then 1 else 0)
    (i l : Fin d) (hl : (l : ℕ) < j) :
    (blkEmb K d j A * M * blkEmb K d j B) i l = if i = l then 1 else 0 := by sorry
