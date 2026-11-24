-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_re_dot_le
-- name    : GlobalTheory.MinorInt.re_dot_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:37.165822+00:00
-- url     : https://prove2.me/theorems/f7a4a666-7d63-4ab1-8c13-a889e74593b6
-- title:
--   Minor Int: re dot le
-- statement:
--   The Minor Int construction uses the re dot le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L124-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L124-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.re_dot_le {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) (x y : ι → ℂ) :
    (star x ⬝ᵥ y).re ≤ c * ∑ i, ‖x i‖ ^ 2 + (∑ i, ‖y i‖ ^ 2) / (4 * c) := by sorry
