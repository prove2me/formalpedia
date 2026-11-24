-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_frobenius
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.surjective_frobenius
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:12.838493+00:00
-- url     : https://prove2.me/theorems/f0afd5d0-e2ee-4838-8919-ed0fffcee713
-- title:
--   Is Perfectoid Field: surjective frobenius
-- statement:
--   The Is Perfectoid Field construction uses the surjective frobenius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L139-L140

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.surjective_frobenius : Function.Surjective (frobenius (ModP (normInteger K) p) p) := by sorry
