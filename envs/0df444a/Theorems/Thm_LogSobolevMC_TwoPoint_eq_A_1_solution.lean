-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_eq_A_1_solution
-- name    : LogSobolevMC.TwoPoint.eq_A_1_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:43.432876+00:00
-- url     : https://prove2.me/theorems/39967e40-c572-4565-b2b9-343e1a830d76
-- title:
--   Proof of Theorem A.2, pp. 745–746 — a = log[(1 − θ)/θ]/(1 − 2θ), s = (1 − 2θ)/(2θ(1 − θ)) solve (A.1)
-- statement:
--   Fix $0<\theta<1/2$ and let $l(s)$ and $e(s)=\theta(1-\theta)s^2$ be the functions of the proof of Theorem A.2 (p. 743–744), namely $\mathcal L$ and $\mathcal E$ of the function taking the values $1+(1-\theta)s$ and $1-\theta s$ on the two-point space with $\pi=(\theta,1-\theta)$. Put
--
--   $$a=\frac{\log[(1-\theta)/\theta]}{1-2\theta},\qquad s=\frac{1-2\theta}{2\theta(1-\theta)}.$$
--
--   Then $s$ is a nonzero point of $[-(1-\theta)^{-1},\theta^{-1}]$ and solves the system
--
--   $$l(s)-a\,e(s)=0,\qquad l'(s)-a\,e'(s)=0. \tag{A.1}$$
--
--   This is the explicit solution that, by the shape analysis of Figure 2, identifies $a=1/\alpha(\theta)$ in Theorem A.2.
--
--   **Formalization Note** $l'$ and $e'$ are the derivatives in $s$ (Lean's `deriv`); both functions are differentiable at this $s$, where $1+(1-\theta)s=1/(2\theta)$ and $1-\theta s=1/(2(1-\theta))$ are positive. The page prints the interval as "$[(1-\theta)^{-1},\theta^{-1}]$"; p. 743 says $s$ varies between $-(1-\theta)^{-1}$ and $\theta^{-1}$, which is the interval used here.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 743–746, proof of Theorem A.2, (A.1) and the displays for a and s on p. 745

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

/-- Proof of Theorem A.2, pp. 745–746: for `0 < θ < 1/2`, `a = log[(1 − θ)/θ]/(1 − 2θ)` and
`s = (1 − 2θ)/(2θ(1 − θ))`, `s` is a nonzero point of `[−(1 − θ)⁻¹, θ⁻¹]` solving the system (A.1)
`l(s) − a e(s) = 0`, `l′(s) − a e′(s) = 0`. -/
theorem eq_A_1_solution (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1 / 2) :
    let a := Real.log ((1 - θ) / θ) / (1 - 2 * θ)
    let s := (1 - 2 * θ) / (2 * θ * (1 - θ))
    s ≠ 0 ∧ -(1 - θ)⁻¹ ≤ s ∧ s ≤ θ⁻¹ ∧
      lFun θ s - a * eFun θ s = 0 ∧
      deriv (lFun θ) s - a * deriv (eFun θ) s = 0 := by sorry

end LogSobolevMC.TwoPoint
