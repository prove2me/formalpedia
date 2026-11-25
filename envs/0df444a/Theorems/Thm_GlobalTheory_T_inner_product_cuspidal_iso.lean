-- Prove2me | Theorems.Thm_GlobalTheory_T_inner_product_cuspidal_iso
-- name    : GlobalTheory.T.inner_product_cuspidal_iso
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:08.937676+00:00
-- url     : https://prove2.me/theorems/ae480a0f-a1bc-4ee1-b5d1-76b8da1e44e4
-- title:
--   T: inner product cuspidal iso
-- statement:
--   The T construction uses the inner product cuspidal iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIsoStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InnerProductCuspidalIsoStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIsoStatement
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

theorem GlobalTheory.T.inner_product_cuspidal_iso : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by sorry
