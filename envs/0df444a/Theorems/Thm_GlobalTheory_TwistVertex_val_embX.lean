-- Prove2me | Theorems.Thm_GlobalTheory_TwistVertex_val_embX
-- name    : GlobalTheory.TwistVertex.val_embX
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:28.662241+00:00
-- url     : https://prove2.me/theorems/4b0af701-f952-4aa8-87c2-8c817b920d2a
-- title:
--   Twist Vertex: val emb X
-- statement:
--   The Twist Vertex construction uses the val emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean#L17-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.TwistVertex.val_embX (g : GL n k) : (embX c g).val = fromBlocks g.val 0 0 1 := by sorry
