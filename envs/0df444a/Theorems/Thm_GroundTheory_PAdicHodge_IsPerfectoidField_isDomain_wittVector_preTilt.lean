-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_wittVector_preTilt
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_wittVector_preTilt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:52.748573+00:00
-- url     : https://prove2.me/theorems/ac9a1984-6c35-4b15-9870-350b099b395d
-- title:
--   Is Perfectoid Field: is Domain witt Vector pre Tilt
-- statement:
--   The Is Perfectoid Field construction uses the is Domain witt Vector pre Tilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L483-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L483-L485

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_wittVector_preTilt : IsDomain 𝕎𝒪♭ := by sorry
