-- Prove2me | Theorems.Thm_GlobalTheory_TwistVertex_mem_level_iff
-- name    : GlobalTheory.TwistVertex.mem_level_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:30.272854+00:00
-- url     : https://prove2.me/theorems/4a43bbd6-8296-44c5-b39f-1b631871e69e
-- title:
--   Twist Vertex: mem level iff
-- statement:
--   The Twist Vertex construction uses the mem level iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean#L53-L65

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}

theorem GlobalTheory.TwistVertex.mem_level_iff (o : r ⊕ e ≃ n ⊕ Fin c) (x : GL (n ⊕ Fin c) k) :
    x ∈ ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J ↔ x ∈ KO k (n ⊕ Fin c) := by sorry
