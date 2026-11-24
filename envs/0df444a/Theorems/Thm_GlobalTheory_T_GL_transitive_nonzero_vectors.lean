-- Prove2me | Theorems.Thm_GlobalTheory_T_GL_transitive_nonzero_vectors
-- name    : GlobalTheory.T.GL_transitive_nonzero_vectors
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:40.613737+00:00
-- url     : https://prove2.me/theorems/2c04d6a2-1867-40ad-b125-3fbaa4fd4576
-- title:
--   T: GL transitive nonzero vectors
-- statement:
--   The T construction uses the GL transitive nonzero vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GLTransitiveNonzeroVectorsStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GLTransitiveNonzeroVectorsStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectors
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectorsStatement
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

theorem GlobalTheory.T.GL_transitive_nonzero_vectors : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by sorry
