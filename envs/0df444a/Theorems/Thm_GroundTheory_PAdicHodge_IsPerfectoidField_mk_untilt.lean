-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.mk_untilt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:53.22914+00:00
-- url     : https://prove2.me/theorems/1f5712ab-6b65-4434-bad7-fc01d6c40fac
-- title:
--   Is Perfectoid Field: mk untilt
-- statement:
--   The Is Perfectoid Field construction uses the mk untilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L151-L153

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.mk_untilt (x : 𝒪♭) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt x) = PreTilt.coeff 0 x := by sorry
