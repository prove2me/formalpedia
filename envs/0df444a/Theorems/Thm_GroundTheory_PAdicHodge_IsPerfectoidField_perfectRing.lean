-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_perfectRing
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.perfectRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:13.491744+00:00
-- url     : https://prove2.me/theorems/144f00a5-8489-4632-8cd8-ca792544ce56
-- title:
--   Is Perfectoid Field: perfect Ring
-- statement:
--   The Is Perfectoid Field construction uses the perfect Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L214-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L214-L238

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

theorem GroundTheory.PAdicHodge.IsPerfectoidField.perfectRing (p : ℕ) [Fact p.Prime] [CharP K p] [IsPerfectoidField K p] :
    PerfectRing K p := by sorry
