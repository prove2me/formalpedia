-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_iterate_succ_pow
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.untilt_iterate_succ_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:59.617002+00:00
-- url     : https://prove2.me/theorems/5384f565-af8e-48e0-b20c-e7c0cc924926
-- title:
--   Is Perfectoid Field: untilt iterate succ pow
-- statement:
--   The Is Perfectoid Field construction uses the untilt iterate succ pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L160-L163

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.untilt_iterate_succ_pow (x : 𝒪♭) (n : ℕ) :
    PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n + 1] x) ^ p =
      PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x) := by sorry
