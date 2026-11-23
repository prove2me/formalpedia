-- Prove2me | Theorems.Thm_GlobalTheory_one_le_sqrt_abs_discr
-- name    : GlobalTheory.one_le_sqrt_abs_discr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:10.133797+00:00
-- url     : https://prove2.me/theorems/89910027-151e-4064-ba77-bcfb2df60fbd
-- title:
--   Global Theory: one le sqrt abs discr
-- statement:
--   The Global Theory construction uses the one le sqrt abs discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L259-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L259-L261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]

theorem GlobalTheory.one_le_sqrt_abs_discr : 1 ≤ √|(discr K : ℝ)| := by sorry
