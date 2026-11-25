-- Prove2me | Theorems.Thm_Newton_lp_duality_pairing
-- name    : Newton.lp_duality_pairing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:09:32.42513+00:00
-- url     : https://prove2.me/theorems/0100f409-5c88-498b-a083-488a354b9af4
-- title:
--   Newton: lp duality pairing
-- statement:
--   Hölder's inequality expressed as a dual pairing between `L^p` and `L^q`.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L28-L40
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L28-L40

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

theorem Newton.lp_duality_pairing
    (p q : ℝ≥0∞) (_hp : 1 < p) (_hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f g : α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ‖∫ x, f x * g x ∂μ‖ ≤
      (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by sorry
