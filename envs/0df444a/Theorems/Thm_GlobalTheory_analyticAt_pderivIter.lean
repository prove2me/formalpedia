-- Prove2me | Theorems.Thm_GlobalTheory_analyticAt_pderivIter
-- name    : GlobalTheory.analyticAt_pderivIter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:34.77251+00:00
-- url     : https://prove2.me/theorems/2dd024c6-c8b3-4c6a-af14-b32b9c266eb4
-- title:
--   Global Theory: analytic At pderiv Iter
-- statement:
--   The Global Theory construction uses the analytic At pderiv Iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L112-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]

theorem GlobalTheory.analyticAt_pderivIter {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α : ι →₀ ℕ) : AnalyticAt 𝕜 (pderivIter α F) a := by sorry
