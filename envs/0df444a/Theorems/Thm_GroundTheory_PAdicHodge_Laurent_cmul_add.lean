-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_add
-- name    : GroundTheory.PAdicHodge.Laurent.cmul_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:18.183922+00:00
-- url     : https://prove2.me/theorems/07ae8953-5cc9-4277-ad6f-7318269b466b
-- title:
--   Laurent: cmul add
-- statement:
--   The Laurent construction uses the cmul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L159-L163

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

theorem GroundTheory.PAdicHodge.Laurent.cmul_add (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul a (b + c) = cmul a b + cmul a c := by sorry
