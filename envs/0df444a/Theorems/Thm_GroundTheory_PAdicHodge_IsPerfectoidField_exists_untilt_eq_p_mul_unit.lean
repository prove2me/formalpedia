-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_untilt_eq_p_mul_unit
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_untilt_eq_p_mul_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:53.084706+00:00
-- url     : https://prove2.me/theorems/33563f0a-236f-4c31-a9eb-221422c7c84e
-- title:
--   Is Perfectoid Field: exists untilt eq p mul unit
-- statement:
--   The Is Perfectoid Field construction uses the exists untilt eq p mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L409-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L409-L436

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
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
variable (K p)

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_untilt_eq_p_mul_unit :
    ∃ ϖ : 𝒪♭, ∃ u : 𝒪, IsUnit u ∧ PreTilt.untilt ϖ = p * u := by sorry
