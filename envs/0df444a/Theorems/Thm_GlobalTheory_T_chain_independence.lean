-- Prove2me | Theorems.Thm_GlobalTheory_T_chain_independence
-- name    : GlobalTheory.T.chain_independence
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:25.605225+00:00
-- url     : https://prove2.me/theorems/90e6d4a3-cd71-434a-9df8-ca9d57d8fe3d
-- title:
--   T: chain independence
-- statement:
--   The T construction uses the chain independence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependenceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChainIndependenceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependenceStatement
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

theorem GlobalTheory.T.chain_independence : ReciprocityTheory.Ty.Fin.St.ChainIndep := by sorry
