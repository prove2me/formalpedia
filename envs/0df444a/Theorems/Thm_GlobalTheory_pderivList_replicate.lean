-- Prove2me | Theorems.Thm_GlobalTheory_pderivList_replicate
-- name    : GlobalTheory.pderivList_replicate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:14.567923+00:00
-- url     : https://prove2.me/theorems/37c31fd5-822b-4a2c-bb06-96b371910e0f
-- title:
--   Global Theory: pderiv List replicate
-- statement:
--   The Global Theory construction uses the pderiv List replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L38-L46

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

theorem GlobalTheory.pderivList_replicate (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivList (List.replicate n k) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by sorry
