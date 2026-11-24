-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_iterate_pow
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.norm_untilt_iterate_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.156354+00:00
-- url     : https://prove2.me/theorems/3bb029c8-28aa-4bce-a50c-a9d5778e7fb0
-- title:
--   Is Perfectoid Field: norm untilt iterate pow
-- statement:
--   The Is Perfectoid Field construction uses the norm untilt iterate pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L165-L168

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.norm_untilt_iterate_pow (x : 𝒪♭) (n : ℕ) :
    ‖((PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x) : 𝒪) : K)‖ ^ p ^ n =
      ‖((PreTilt.untilt x : 𝒪) : K)‖ := by sorry
