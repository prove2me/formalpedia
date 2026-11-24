-- Prove2me | Theorems.Thm_GlobalTheory_T_intertwiner_inner_product
-- name    : GlobalTheory.T.intertwiner_inner_product
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:47:18.832336+00:00
-- url     : https://prove2.me/theorems/d97a9bad-b165-455c-8203-0e0719c80cfa
-- title:
--   T: intertwiner inner product
-- statement:
--   The T construction uses the intertwiner inner product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntertwinerInnerProductStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntertwinerInnerProductStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProduct
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProductStatement
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

theorem GlobalTheory.T.intertwiner_inner_product : ReciprocityTheory.Ty.Fin.St.IntwIp := by sorry
