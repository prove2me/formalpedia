-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.preTilt_ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:35.246124+00:00
-- url     : https://prove2.me/theorems/c1f09d3c-832f-4248-b90b-54dc40384ccd
-- title:
--   Is Perfectoid Field: pre Tilt ext
-- statement:
--   The Is Perfectoid Field construction uses the pre Tilt ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L148-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L148-L149

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.preTilt_ext {x y : 𝒪♭} (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) : x = y := by sorry
