-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_twoBlock_surjective
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspSum.twoBlock_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:19.265567+00:00
-- url     : https://prove2.me/theorems/ad8ed37c-d56c-4a64-bde2-fb45061ac4e8
-- title:
--   Cusp Sum: two Block surjective
-- statement:
--   The Cusp Sum construction uses the two Block surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalUnipotentRadicalSumZero.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalUnipotentRadicalSumZero.lean#L66-L71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspSum
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem GlobalTheory.CompanionTheory.TyFin.CuspSum.twoBlock_surjective {d j : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    Function.Surjective (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by sorry
