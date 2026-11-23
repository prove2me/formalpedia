-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ne_zero_of_mem_domSet
-- name    : GroundTheory.PAdicHodge.Laurent.ne_zero_of_mem_domSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:32.370272+00:00
-- url     : https://prove2.me/theorems/d966a4eb-ce1a-43e3-b83f-68fea7bc6275
-- title:
--   Laurent: ne zero of mem dom Set
-- statement:
--   The Laurent construction uses the ne zero of mem dom Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L314-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L314-L318

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
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
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem GroundTheory.PAdicHodge.Laurent.ne_zero_of_mem_domSet {n : ℤ} (hn : n ∈ domSet a ρ) : a n ≠ 0 := by sorry
