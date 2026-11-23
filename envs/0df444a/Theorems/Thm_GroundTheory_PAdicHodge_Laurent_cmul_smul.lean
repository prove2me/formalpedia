-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_smul
-- name    : GroundTheory.PAdicHodge.Laurent.cmul_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:42.11539+00:00
-- url     : https://prove2.me/theorems/a87a9b5e-f2b1-4ebe-85d0-ad663864f20e
-- title:
--   Laurent: cmul smul
-- statement:
--   The Laurent construction uses the cmul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L175-L179

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
variable [CompleteSpace K]

theorem GroundTheory.PAdicHodge.Laurent.cmul_smul (k : K) (a b : ℤ → K) : cmul a (k • b) = k • cmul a b := by sorry
