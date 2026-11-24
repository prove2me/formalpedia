-- Prove2me | Theorems.Thm_GlobalTheory_KSp_OpenCrit_tendsto_nOf
-- name    : GlobalTheory.KSp.OpenCrit.tendsto_nOf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:41.623136+00:00
-- url     : https://prove2.me/theorems/1b6fbd14-7d5f-4271-ac59-0193cf9f7185
-- title:
--   Open Crit: tendsto n Of
-- statement:
--   The Open Crit construction uses the tendsto n Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSubgroupOfSiegelAndOppositeNhds.lean#L116-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSubgroupOfSiegelAndOppositeNhds.lean#L116-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.OpenCrit
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]
variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

theorem GlobalTheory.KSp.OpenCrit.tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by sorry
