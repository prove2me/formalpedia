-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_untilt
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_iff_norm_untilt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:12.160367+00:00
-- url     : https://prove2.me/theorems/13d32a99-f21e-413e-bcfc-8503016f4285
-- title:
--   Is Perfectoid Field: is Unit iff norm untilt
-- statement:
--   The Is Perfectoid Field construction uses the is Unit iff norm untilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L229-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L229-L239

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_iff_norm_untilt {x : 𝒪♭} : IsUnit x ↔ ‖((PreTilt.untilt x : 𝒪) : K)‖ = 1 := by sorry
