-- Prove2me | Theorems.Thm_GlobalTheory_T_mackey_inner_product
-- name    : GlobalTheory.T.mackey_inner_product
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:51:56.533327+00:00
-- url     : https://prove2.me/theorems/83f9697f-f4ca-43e1-ae64-a4046862f33e
-- title:
--   T: mackey inner product
-- statement:
--   The T construction uses the mackey inner product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProductStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProductStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProductStatement
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

theorem GlobalTheory.T.mackey_inner_product : ReciprocityTheory.Ty.Fin.St.MackeyIp := by sorry
