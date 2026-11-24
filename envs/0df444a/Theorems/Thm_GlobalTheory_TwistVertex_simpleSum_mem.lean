-- Prove2me | Theorems.Thm_GlobalTheory_TwistVertex_simpleSum_mem
-- name    : GlobalTheory.TwistVertex.simpleSum_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:08.023301+00:00
-- url     : https://prove2.me/theorems/43e25b9d-e075-4ae3-a7e9-6bc661ed7e5b
-- title:
--   Twist Vertex: simple Sum mem
-- statement:
--   The Twist Vertex construction uses the simple Sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FirstVertexParahoricLevelChainTwist.lean#L41-L45

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
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.TwistVertex.simpleSum_mem {u : GL (n ⊕ Fin c) k} (hu : u ∈ KO k (n ⊕ Fin c)) : simpleSum u ∈ 𝒪[k] := by sorry
