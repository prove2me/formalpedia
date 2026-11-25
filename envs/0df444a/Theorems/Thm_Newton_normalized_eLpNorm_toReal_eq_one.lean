-- Prove2me | Theorems.Thm_Newton_normalized_eLpNorm_toReal_eq_one
-- name    : Newton.normalized_eLpNorm_toReal_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:09:38.01641+00:00
-- url     : https://prove2.me/theorems/eac78a4a-eece-4bce-b287-9143a3e7051b
-- title:
--   Newton: normalized e Lp Norm to Real eq one
-- statement:
--   Scaling `f` by the reciprocal of its `L^p` norm yields a unit `eLpNorm`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L43-L62
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L43-L62

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Newton.normalized_eLpNorm_toReal_eq_one
    (p : ℝ≥0∞) {f : α → ℝ} (hf_ne_zero : (eLpNorm f p μ).toReal ≠ 0) :
    (eLpNorm (fun x => (1 / (eLpNorm f p μ).toReal) * f x) p μ).toReal = 1 := by sorry
