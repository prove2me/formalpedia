-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_actual_geometric_sharpness_calculation
-- name    : K24.Global.FlatTorus.actual_geometric_sharpness_calculation
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:59:32.232677+00:00
-- url     : https://prove2.me/theorems/f8ab25d1-70f2-4678-91d4-6cb1008ca3b3
-- title:
--   K24 actual flat-torus Lie–Bianchi defect and two-point Hölder quotient
-- statement:
--   On the flat four-torus with its actual quotient atlas, put
--   $$a_n=n^{-(3+\alpha)},\qquad f_n(r)=a_n\sin(nr),\qquad h_n=f_n(x_1)\,dx_1^2,\qquad V=\cos(x_2)\partial_1.$$
--   Use the frozen Bianchi convention $\beta=-\operatorname{div}+\tfrac12d\operatorname{tr}$. The first assertion identifies the pullback of the actual geometric covector $\beta_{g_0}(\mathcal L_V h_n)$ at every lift:
--   $$\bigl(\cos(x_2)(f_n(x_1)-\tfrac12 f_n''(x_1)),\ \tfrac12\sin(x_2)f_n'(x_1),\ 0,\ 0\bigr).$$
--   This identity holds for every real $\alpha$ and every natural $n$, with Lean's total real-power convention at zero. No coefficient identity or smooth-atlas premise is assumed.
--
--   For $0<\alpha<1$ and $n\ge2$, let $d(x)$ be the $x_1$ derivative of the first component of that actual pullback and let $y=(\pi/n)e_1$. The second assertion is
--   $$\frac{|d(0)-d(y)|}{\operatorname{dist}(0,y)^\alpha}=\left(1+\frac{2}{n^2}\right)\pi^{-\alpha}.$$
--   Lean coordinates 0 and 1 correspond to the source coordinates $x_1$ and $x_2$.
--
--   This gives the actual geometric calculation used in K24 §5.1. The full sharpness theorem additionally requires the marked circle action, Haar cancellation, finite full Hölder norms, metric positivity, uniform upper estimates, convergence, and the final failure of a uniform operator estimate.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §5.1, equations (5.6)–(5.8).

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus

theorem actual_geometric_sharpness_calculation :
    (∀ (alpha : ℝ) (n : ℕ) (x : FourSpace),
      coverCovector (unprojectedDefect alpha n) x = expectedDefectCoefficients alpha n x) ∧
    (∀ (alpha : HolderExponent) (n : ℕ), 2 ≤ n →
      let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
      let d : FourSpace → ℝ := fun x =>
        coordDeriv (fun z => coverCovector (unprojectedDefect alpha.value n) z 0) 0 x
      |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha.value =
        (1 + 2 / (n : ℝ) ^ 2) * Real.rpow Real.pi (-(alpha.value : ℝ))) := by
  sorry

end K24.Global.FlatTorus
