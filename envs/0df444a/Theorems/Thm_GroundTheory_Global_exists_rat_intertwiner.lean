-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_rat_intertwiner
-- name    : GroundTheory.Global.exists_rat_intertwiner
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:47.521659+00:00
-- url     : https://prove2.me/theorems/15c88241-4273-4270-9218-adcea014f933
-- title:
--   Global: exists rat intertwiner
-- statement:
--   The Global construction uses the exists rat intertwiner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/RationalForm.lean#L7-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/RationalForm.lean#L7-L105

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Matrix

theorem GroundTheory.Global.exists_rat_intertwiner {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (A A' : J → Matrix ι ι ℚ) (P : Matrix ι ι ℝ) (hP : P.det ≠ 0)
    (h : ∀ j, P * (A j).map (Rat.cast : ℚ → ℝ) = (A' j).map (Rat.cast : ℚ → ℝ) * P) :
    ∃ Q : Matrix ι ι ℚ, Q.det ≠ 0 ∧ ∀ j, Q * A j = A' j * Q := by sorry
