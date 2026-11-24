-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_dvd_of_norm_untilt_le
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.dvd_of_norm_untilt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:29.479163+00:00
-- url     : https://prove2.me/theorems/d028469c-dbbf-47f9-a7d6-862c669fa7f0
-- title:
--   Is Perfectoid Field: dvd of norm untilt le
-- statement:
--   The Is Perfectoid Field construction uses the dvd of norm untilt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L198-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L198-L227

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
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
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "φ" => RingEquiv.symm (frobeniusEquiv (PreTilt (normInteger K) p) p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.dvd_of_norm_untilt_le {a b : 𝒪♭} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : 𝒪) : K)‖ ≤ ‖((PreTilt.untilt b : 𝒪) : K)‖) : b ∣ a := by sorry
