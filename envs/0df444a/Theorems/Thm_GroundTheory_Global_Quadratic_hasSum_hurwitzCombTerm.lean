-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_hasSum_hurwitzCombTerm
-- name    : GroundTheory.Global.Quadratic.hasSum_hurwitzCombTerm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:20.102064+00:00
-- url     : https://prove2.me/theorems/f7a543ab-0761-4916-b861-e3588f264a59
-- title:
--   Quadratic: has Sum hurwitz Comb Term
-- statement:
--   The Quadratic construction uses the has Sum hurwitz Comb Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L114-L124

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic

theorem GroundTheory.Global.Quadratic.hasSum_hurwitzCombTerm {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ hurwitzCombTerm x n s) (hurwitzComb x s) := by sorry
