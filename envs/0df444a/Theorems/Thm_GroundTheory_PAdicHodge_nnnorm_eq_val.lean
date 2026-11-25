-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nnnorm_eq_val
-- name    : GroundTheory.PAdicHodge.nnnorm_eq_val
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:47.044151+00:00
-- url     : https://prove2.me/theorems/1f9d752b-3c11-4fbf-9055-6c0993969d71
-- title:
--   PAdic Hodge: nnnorm eq val
-- statement:
--   The PAdic Hodge construction uses the nnnorm eq val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean#L115-L117

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.nnnorm_eq_val (x : PreTilt (normInteger K) p) :
    ‖x‖₊ = PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p x := by sorry
