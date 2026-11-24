-- Prove2me | Theorems.Thm_GlobalTheory_CosetFn_mul_embX_mem_R
-- name    : GlobalTheory.CosetFn.mul_embX_mem_R
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:30.390522+00:00
-- url     : https://prove2.me/theorems/46dd9c55-9d24-4232-8f67-f633217b2f38
-- title:
--   Coset Fn: mul emb X mem R
-- statement:
--   The Coset Fn construction uses the mul emb X mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsParabolicDoubleCosetFunctionEqOne.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsParabolicDoubleCosetFunctionEqOne.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsParabolicDoubleCosetFunctionEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.CosetFn
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CosetFn.mul_embX_mem_R {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (g : GL n k) :
    u * embX c g ∈ R k n c 1 := by sorry
