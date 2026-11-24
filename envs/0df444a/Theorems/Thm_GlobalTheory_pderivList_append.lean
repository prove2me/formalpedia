-- Prove2me | Theorems.Thm_GlobalTheory_pderivList_append
-- name    : GlobalTheory.pderivList_append
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:47.916084+00:00
-- url     : https://prove2.me/theorems/a54677d9-daed-48b6-b747-179f2d46388c
-- title:
--   Global Theory: pderiv List append
-- statement:
--   The Global Theory construction uses the pderiv List append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L24-L26

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
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem GlobalTheory.pderivList_append (l₁ l₂ : List ι) (F : (ι → 𝕜) → V) :
    pderivList (l₁ ++ l₂) F = pderivList l₁ (pderivList l₂ F) := by sorry
