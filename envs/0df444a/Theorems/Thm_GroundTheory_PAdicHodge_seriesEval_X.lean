-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_X
-- name    : GroundTheory.PAdicHodge.seriesEval_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:54.592815+00:00
-- url     : https://prove2.me/theorems/744e8fa8-8160-4cfd-b44f-6558c913509b
-- title:
--   PAdic Hodge: series Eval X
-- statement:
--   The PAdic Hodge construction uses the series Eval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L141-L148

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}

theorem GroundTheory.PAdicHodge.seriesEval_X {z : B} (hz : z ∈ I) : seriesEval I z hz X = z := by sorry
