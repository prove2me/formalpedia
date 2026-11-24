-- Prove2me | Theorems.Thm_GlobalTheory_T_separable_irreducible
-- name    : GlobalTheory.T.separable_irreducible
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:08.82978+00:00
-- url     : https://prove2.me/theorems/d962c0d4-733f-4b82-a2d0-08e271305df0
-- title:
--   T: separable irreducible
-- statement:
--   The T construction uses the separable irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducibleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducibleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.separable_irreducible : ReciprocityTheory.Ty.Fin.St.SepIrr := by sorry
