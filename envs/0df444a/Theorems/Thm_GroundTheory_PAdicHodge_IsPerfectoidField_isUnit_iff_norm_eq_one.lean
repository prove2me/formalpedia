-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_eq_one
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_iff_norm_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:35.030504+00:00
-- url     : https://prove2.me/theorems/29ad8ebe-528e-4686-9e05-d7862475bfca
-- title:
--   Is Perfectoid Field: is Unit iff norm eq one
-- statement:
--   The Is Perfectoid Field construction uses the is Unit iff norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L84-L97

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
variable {p}

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_iff_norm_eq_one {u : 𝒪} : IsUnit u ↔ ‖(u : K)‖ = 1 := by sorry
