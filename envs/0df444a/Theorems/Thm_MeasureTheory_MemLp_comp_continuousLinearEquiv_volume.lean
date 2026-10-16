-- Prove2me | Theorems.Thm_MeasureTheory_MemLp_comp_continuousLinearEquiv_volume
-- name    : MeasureTheory.MemLp.comp_continuousLinearEquiv_volume
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:32:17.068196+00:00
-- url     : https://prove2.me/theorems/9e64248a-7d85-4309-b9c1-fdd9392de249
-- title:
--   Invertible real linear changes of variables preserve Lp membership
-- statement:
--   Let E be a finite-dimensional real inner product space with its Borel Lebesgue measure, let e be a continuous linear automorphism, and let p be any extended nonnegative exponent. If f is a real-valued Lp function, then f composed with e is also Lp. No restriction on p is needed, including p=0 and p=infinity. The pushforward of volume is a finite positive scalar multiple of volume, given by the inverse absolute determinant.
-- source:
--   Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, MeasureTheory/Measure/Lebesgue/EqHaar.lean, map_linearMap_addHaar_eq_smul_addHaar, and MeasureTheory/Function/LpSeminorm/Basic.lean, MemLp.smul_measure and MemLp.comp_of_map. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L231

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem MeasureTheory.MemLp.comp_continuousLinearEquiv_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : E ≃L[ℝ] E) (p : ℝ≥0∞) (f : E → ℝ) (hf : MemLp f p volume) :
    MemLp (fun x => f (e x)) p volume := by sorry
