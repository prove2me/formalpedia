-- Prove2me | Theorems.Thm_NoHair_KNE_thm_div_two
-- name    : NoHair.KNE.thm_div_two
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-13T08:26:17.924173+00:00
-- url     : https://prove2.me/theorems/36d617c4-dee0-4ad2-a404-b36e7ef9f8df
-- title:
--   Kerr–Newman closed-form Christoffel symbols: divergence in direction 2
-- statement:
--   For all real $m,a,e$ and every point $y$ with $r(y)>0$, the closed-form Christoffel symbols `Gam` (block `NoHair_KerrNewmanEinstein_Base`) composed with the atoms $w\mapsto(r(w),k_1(w),k_2(w),k_3(w),W(w))$ satisfy: the functions $\Gamma^{2}_{2\sigma}$ are differentiable at $y$, and the coordinate partial $\partial_2\Gamma^2_{\nu\sigma}(y)$ equals the closed form `dDivT` for all $\nu,\sigma$.
--
--   This is an intermediate step in the machine-checked proof of `NoHair.kerrNewman_einstein` (Kerr–Newman satisfies the Einstein equation in Kerr–Schild coordinates). Its proof uses the definition blocks `NoHair_KerrNewmanEinstein_Div3`.
-- source:
--   Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*; Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, https://doi.org/10.1063/1.1704351.

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem thm_div_two (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    (∀ σ, DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 2 2 σ) y) ∧
    (∀ ν σ, coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) 2 ν σ) 2 y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) 2 ν σ) := by
  sorry

end NoHair.KNE
