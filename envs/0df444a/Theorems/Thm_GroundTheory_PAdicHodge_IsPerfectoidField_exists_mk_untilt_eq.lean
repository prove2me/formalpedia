-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mk_untilt_eq
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.exists_mk_untilt_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:37.072999+00:00
-- url     : https://prove2.me/theorems/328e74ff-090d-4e7c-931e-407544671e69
-- title:
--   Is Perfectoid Field: exists mk untilt eq
-- statement:
--   The Is Perfectoid Field construction uses the exists mk untilt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L241-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L241-L247

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.exists_mk_untilt_eq (b : 𝒪) :
    ∃ a : 𝒪♭, Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt a) =
      Ideal.Quotient.mk _ b := by sorry
