-- Prove2me | Theorems.Thm_GlobalTheory_five_elementary_inequalities_eventually
-- name    : GlobalTheory.five_elementary_inequalities_eventually
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:55:42.81818+00:00
-- url     : https://prove2.me/theorems/2663e6f0-f5be-5f4d-a0df-bfcf3eaf71a9
-- title:
--   Global Theory: five elementary inequalities eventually
-- statement:
--   The Global Theory construction uses the five elementary inequalities eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiveElementaryInequalitiesEventually.lean#L23-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiveElementaryInequalitiesEventually.lean#L23-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Real
open GlobalTheory

theorem GlobalTheory.five_elementary_inequalities_eventually :
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧
      11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧
      2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧
      44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by sorry
