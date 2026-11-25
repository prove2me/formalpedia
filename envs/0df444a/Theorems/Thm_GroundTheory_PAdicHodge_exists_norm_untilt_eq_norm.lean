-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq_norm
-- name    : GroundTheory.PAdicHodge.exists_norm_untilt_eq_norm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:24.63272+00:00
-- url     : https://prove2.me/theorems/6775775c-eaa3-4aed-a8d5-e868beed0679
-- title:
--   PAdic Hodge: exists norm untilt eq norm
-- statement:
--   The PAdic Hodge construction uses the exists norm untilt eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L255-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L255-L257

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
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
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)

theorem GroundTheory.PAdicHodge.exists_norm_untilt_eq_norm {y : K} (hy0 : y ≠ 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ a : 𝒪♭, ‖♮a‖ = ‖y‖ := by sorry
