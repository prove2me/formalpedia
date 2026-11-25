-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_limPunctured
-- name    : GroundTheory.Global.Elliptic.analyticAt_limPunctured
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:26.048548+00:00
-- url     : https://prove2.me/theorems/64b7a142-bc1f-4f97-8d39-440ffa69416d
-- title:
--   Elliptic: analytic At lim Punctured
-- statement:
--   The Elliptic construction uses the analytic At lim Punctured property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean#L32-L41

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]

theorem GroundTheory.Global.Elliptic.analyticAt_limPunctured [CompleteSpace E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) : AnalyticAt ℂ (limPunctured f) z := by sorry
