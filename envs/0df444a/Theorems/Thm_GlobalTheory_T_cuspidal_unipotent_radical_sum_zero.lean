-- Prove2me | Theorems.Thm_GlobalTheory_T_cuspidal_unipotent_radical_sum_zero
-- name    : GlobalTheory.T.cuspidal_unipotent_radical_sum_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:18.926844+00:00
-- url     : https://prove2.me/theorems/a32fdd78-b597-4d47-942e-bbf7557b7b09
-- title:
--   T: cuspidal unipotent radical sum zero
-- statement:
--   The T construction uses the cuspidal unipotent radical sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalUnipotentRadicalSumZeroStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalUnipotentRadicalSumZeroStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cuspidal_unipotent_radical_sum_zero : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by sorry
