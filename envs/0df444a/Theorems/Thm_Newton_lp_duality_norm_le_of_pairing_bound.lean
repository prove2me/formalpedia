-- Prove2me | Theorems.Thm_Newton_lp_duality_norm_le_of_pairing_bound
-- name    : Newton.lp_duality_norm_le_of_pairing_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:51:49.799984+00:00
-- url     : https://prove2.me/theorems/e5980371-c806-431f-ab96-736316b37a2d
-- title:
--   Newton: lp duality norm le of pairing bound
-- statement:
--   Control the `L^p` norm of `f` by bounding pairings against the unit ball of `L^q`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L617-L650
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L617-L650

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

theorem Newton.lp_duality_norm_le_of_pairing_bound
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ)
    {B : ℝ}
    (hB : ∀ g : α → ℝ,
      MemLp g q μ →
      (eLpNorm g q μ).toReal ≤ 1 →
      Integrable (fun x => f x * g x) μ →
      |∫ x, f x * g x ∂μ| ≤ B) :
    (eLpNorm f p μ).toReal ≤ B := by sorry
