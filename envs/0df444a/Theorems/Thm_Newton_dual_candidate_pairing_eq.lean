-- Prove2me | Theorems.Thm_Newton_dual_candidate_pairing_eq
-- name    : Newton.dual_candidate_pairing_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:11:42.808734+00:00
-- url     : https://prove2.me/theorems/f88bde29-c468-48f2-ac22-4467fdd94b2e
-- title:
--   Newton: dual candidate pairing eq
-- statement:
--   The Hölder extremiser realises the dual pairing for a unit `L^p` function.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L240-L465
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Function/LpSpace/Duality.lean#L240-L465

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

theorem Newton.dual_candidate_pairing_eq
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ)
    (hf_norm : (eLpNorm f p μ).toReal = 1) :
    (∫ x, f x *
        (Real.sign (f x) * |f x| ^ (p.toReal - 1)) ∂μ)
      =
        (eLpNorm f p μ).toReal *
          (eLpNorm (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ).toReal ∧
      (eLpNorm (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ).toReal = 1 := by sorry
