-- Prove2me | Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
-- name    : MasulloRH.prime_ramp_integrated_explicit_formula
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:57:36.965198+00:00
-- url     : https://prove2.me/theorems/46bfb4c3-d0d0-4f45-8cc0-78976bcb1803
-- title:
--   An absolutely convergent explicit formula for increments of the corrected prime ramp
-- statement:
--   Write G(x) = Σₙ≤ₓ Λ(n)(x/n−1)₊ − x(log x−1−γ). For every x≥1 the series K(x,ρ)=mρ x^(ρ−1)/(ρ(ρ−1)) over all distinct nontrivial zeta zeros converges absolutely. For 2≤a≤b, G(b)/b−G(a)/a is exactly minus the sum of K(b,ρ)−K(a,ρ) and minus the integral from a to b of [log(2π)+(1/2)log(1−t⁻²)]/t². No zero-location or simplicity assumption is imposed.
-- source:
--   For the corrected ramp of MasulloRH.smoothed_prime_ramp_upper_windows. Integrates the accepted GuthMaynard.davenport_truncated_explicit_formula (https://prove2.me/theorems/f087183c-55f6-4452-bdfb-39d3a06edd5c) against t⁻² on compact positive intervals. Dominated convergence discards the countable set of integer discontinuities. Abel summation identifies the arithmetic primitive. Weighted zero summability and a zero-free low rectangle imply absolute convergence.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory
open scoped Interval
namespace MasulloRH

theorem prime_ramp_integrated_explicit_formula :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let K (x : ℝ) (ρ : ZetaZerosInTraceStrip (1/2)) :=
      (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))
    (∀ x : ℝ, 1≤x → Summable (fun ρ => ‖K x ρ‖)) ∧
    (∀ a b : ℝ, 2≤a → a≤b →
      ((G b/b - G a/a:ℝ):ℂ) + (∑' ρ : ZetaZerosInTraceStrip (1/2),(K b ρ-K a ρ)) +
        (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) = 0) := by sorry

end MasulloRH
