-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq
-- name    : GroundTheory.PAdicHodge.exists_norm_untilt_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:35.054496+00:00
-- url     : https://prove2.me/theorems/8e53a6dd-ab1a-44a1-b752-b9dfeb33526e
-- title:
--   PAdic Hodge: exists norm untilt eq
-- statement:
--   The PAdic Hodge construction uses the exists norm untilt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean#L286-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltValuation.lean#L286-L294

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

theorem GroundTheory.PAdicHodge.exists_norm_untilt_eq (a : normInteger K) (ha : ‖(p : K)‖ < ‖(a : K)‖) :
    ∃ x : PreTilt (normInteger K) p, ‖((x.untilt : normInteger K) : K)‖ = ‖(a : K)‖ := by sorry
