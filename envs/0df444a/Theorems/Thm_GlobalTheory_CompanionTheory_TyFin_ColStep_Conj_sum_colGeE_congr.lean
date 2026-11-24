-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_sum_colGeE_congr
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.sum_colGeE_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:09.943484+00:00
-- url     : https://prove2.me/theorems/d75b5e3c-f93f-4ba8-9239-87e525131170
-- title:
--   Conj: sum col Ge E congr
-- statement:
--   The Conj construction uses the sum col Ge E congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L155-L162

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.sum_colGeE_congr {d j : ℕ} (X U : Matrix (Fin d) (Fin d) K)
    (hXU : ∀ i l : Fin d, j ≤ (i : ℕ) → j ≤ (l : ℕ) → X i l = U i l) :
    ∑ i, ∑ l, colGeE K d (j + 1) i l * X i l = ∑ i, ∑ l, colGeE K d (j + 1) i l * U i l := by sorry
