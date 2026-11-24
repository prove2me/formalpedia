-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_nonempty_of_mem_codiscrete
-- name    : GroundTheory.Global.Elliptic.nonempty_of_mem_codiscrete
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:41.170703+00:00
-- url     : https://prove2.me/theorems/56ba8e20-2047-4071-a90d-5b3ae0c58798
-- title:
--   Elliptic: nonempty of mem codiscrete
-- statement:
--   The Elliptic construction uses the nonempty of mem codiscrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AnalyticAlgebraicGerm.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AnalyticAlgebraicGerm.lean#L34-L37

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem GroundTheory.Global.Elliptic.nonempty_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) : S.Nonempty := by sorry
