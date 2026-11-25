-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_eval_line
-- name    : GlobalTheory.hasDerivAt_eval_line
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:03.160896+00:00
-- url     : https://prove2.me/theorems/63f34005-3dde-53d9-9f59-339da817cd01
-- title:
--   Global Theory: has Deriv At eval line
-- statement:
--   The Global Theory construction uses the has Deriv At eval line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L133-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L133-L153

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

theorem GlobalTheory.hasDerivAt_eval_line (Q : MvPolynomial ι 𝕜) (z : ι → 𝕜) (k : ι) :
    HasDerivAt (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) Q)
      (MvPolynomial.eval z (MvPolynomial.pderiv k Q)) 0 := by sorry
