-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_preTilt
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:38.318428+00:00
-- url     : https://prove2.me/theorems/d5b9a710-c1dc-4b11-973b-9e50d646c8c5
-- title:
--   Is Perfectoid Field: is Domain pre Tilt
-- statement:
--   The Is Perfectoid Field construction uses the is Domain pre Tilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L145-L146

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
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
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt : IsDomain (PreTilt (normInteger K) p) := by sorry
