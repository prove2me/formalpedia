-- Prove2me | Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy
-- name    : MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:29:41.640628+00:00
-- url     : https://prove2.me/theorems/d932ffd5-c07c-4344-a652-a0e637e32bae
-- title:
--   Riemann Hypothesis is equivalent to an 81 bound for all finite square-sampled prime energies
-- statement:
--   Let G be the corrected von Mangoldt prime ramp. For integers k≥4 set aₖ=G(k²)²/[k³(1+log k)²]. Ordinary RH is equivalent to convergence of Σ aₖ, and equivalently to every finite initial sum being at most 81. Unconditionally, |G(y)−G(x)|≤46(y−x) for 4≤x≤y≤2x. The square-sampled series contains only arithmetic data and Euler’s constant.
-- source:
--   Discretization of MasulloRH.riemannHypothesis_iff_prime_ramp_log_energy (0764b70c). The secant estimate 79af092f and unconditional linear bound from 69c40bb0 control the variation of G between adjacent squares. The reciprocal-logarithm telescoping estimate makes the discretization errors square integrable and yields the fixed finite-sum cap 81.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem riemannHypothesis_iff_square_sampled_prime_energy :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let a (n : ℕ) := let k := (n:ℝ)+4
      (G (k^2))^2/(k^3*(1+Real.log k)^2)
    (RiemannHypothesis ↔ Summable a) ∧
    (RiemannHypothesis ↔ ∀ N : ℕ,(∑ n ∈ range N,a n) ≤ 81) ∧
    (∀ x y : ℝ,4 ≤ x → x ≤ y → y ≤ 2*x → |G y-G x| ≤ 46*(y-x)) := by sorry

end MasulloRH
