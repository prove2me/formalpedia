-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_RowTrans_gl_transitive_rows
-- name    : GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:53.531798+00:00
-- url     : https://prove2.me/theorems/07c7bda6-6f22-4465-b8a8-1667833505e4
-- title:
--   Row Trans: gl transitive rows
-- statement:
--   The Row Trans construction uses the gl transitive rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GLTransitiveNonzeroVectors.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GLTransitiveNonzeroVectors.lean#L22-L39

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.RowTrans

theorem GlobalTheory.CompanionTheory.TyFin.RowTrans.gl_transitive_rows : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (r r' : Fin j → K), r ≠ 0 → r' ≠ 0 →
    ∃ g : GL (Fin j) K, Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K) = r' := by sorry
