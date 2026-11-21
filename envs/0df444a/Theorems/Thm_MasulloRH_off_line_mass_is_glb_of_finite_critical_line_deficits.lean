-- Prove2me | Theorems.Thm_MasulloRH_off_line_mass_is_glb_of_finite_critical_line_deficits
-- name    : MasulloRH.off_line_mass_is_glb_of_finite_critical_line_deficits
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:24:16.000608+00:00
-- url     : https://prove2.me/theorems/d5f04d5e-59b6-4b60-9d22-08e76e0e7533
-- title:
--   The off-line reference mass is the greatest lower bound of finite critical-line prime deficits
-- statement:
--   Subtract the kernel mass of any finite critical-line set from the full corrected prime series. The greatest lower bound of all these deficits is exactly the real reference-resolvent mass of the off-line zeros, the limiting theta cutoff discrepancy.
-- source:
--   https://prove2.me/theorems/f6ad556e-8b16-4c16-804f-1206003a7a7a

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction Set

namespace MasulloRH
theorem off_line_mass_is_glb_of_finite_critical_line_deficits :
    let C := Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑' j : ℕ, (vonMangoldt j/(j:ℝ)^(5/2:ℝ) - vonMangoldt j/(j:ℝ)^(3:ℝ)))
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    IsGLB (Set.range (fun F => C - M F))
      (∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
        (zeroResolventTerm (1/2) 3 z.val).re) := by sorry
end MasulloRH
