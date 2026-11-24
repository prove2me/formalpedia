-- Prove2me | Theorems.Thm_GlobalTheory_update_eq_add_smul_single
-- name    : GlobalTheory.update_eq_add_smul_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:52.802693+00:00
-- url     : https://prove2.me/theorems/9961c047-d06b-431b-bed9-ffa549cc0f62
-- title:
--   Global Theory: update eq add smul single
-- statement:
--   The Global Theory construction uses the update eq add smul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L31-L36

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

theorem GlobalTheory.update_eq_add_smul_single (z : ι → 𝕜) (k : ι) (t : 𝕜) :
    Function.update z k t = z + (t - z k) • (Pi.single k 1 : ι → 𝕜) := by sorry
