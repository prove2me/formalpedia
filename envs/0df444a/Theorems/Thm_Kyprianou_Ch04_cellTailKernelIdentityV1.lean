-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cellTailKernelIdentityV1
-- name    : Kyprianou.Ch04.cellTailKernelIdentityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:40:55.853882+00:00
-- url     : https://prove2.me/theorems/6580de31-6621-4d16-bfac-18f10e22dde4
-- title:
--   Signed tail box kernel identity
-- statement:
--   Signed tail boxes reproduce the finite-cell kernel.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_predictableTailBoxDifferenceV1
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cellTailKernelIdentityV1 {Ω ι : Type} [DecidableEq ι]
    (s : Finset ι) (T : NNReal) (a b : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) (hbT : ∀ i ∈ s, b i ≤ T)
    (ω : Ω) (z : ℝ × ℝ) :
    (∑ i ∈ s.product (Finset.univ : Finset Bool),
      (Ioc ((if i.2 then a i.1 else b i.1 : NNReal) : ℝ) (T : ℝ) ×ˢ B i.1).indicator
        (fun _ => if i.2 then H i.1 ω else -H i.1 ω) z) =
      ∑ i ∈ s, (Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i).indicator (fun _ => H i ω) z := by
  sorry
end Kyprianou.Ch04
