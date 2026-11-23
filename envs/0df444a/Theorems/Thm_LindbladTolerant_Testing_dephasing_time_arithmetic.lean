-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_dephasing_time_arithmetic
-- name    : LindbladTolerant.Testing.dephasing_time_arithmetic
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:04:28.385425+00:00
-- url     : https://prove2.me/theorems/4b6bd224-5a49-4c36-b1ab-8d120fa12803
-- title:
--   Theorem 5.2 — explicit time bound from the Hellinger estimate
-- statement:
--   Let $0\le\varepsilon_1<\varepsilon_2$, $T\ge0$, and set the dephasing rates
--   $$
--   \Gamma_0=\frac{\varepsilon_1}{\sqrt2},\qquad
--   \Gamma_1=\frac{\varepsilon_2}{\sqrt2}.
--   $$
--   If the Poisson count distance at time $T$ is at least $1/3$ and obeys the Hellinger upper bound, then, with $c=\sqrt2\log(9/8)$ and $\Delta=\varepsilon_2-\varepsilon_1$,
--   $$
--   T\ge c\,\frac{(\sqrt{\varepsilon_2}+\sqrt{\varepsilon_1})^2}{\Delta^2}
--    \ge c\,\frac{\varepsilon_2}{\Delta^2}.
--   $$
--
--   The separation and upper bound imply
--   $$
--   \exp\!\left[-T(\sqrt{\Gamma_1}-\sqrt{\Gamma_0})^2\right]\le\frac89.
--   $$
--   Taking logarithms and using $\varepsilon_2-\varepsilon_1=(\sqrt{\varepsilon_2}+\sqrt{\varepsilon_1})(\sqrt{\varepsilon_2}-\sqrt{\varepsilon_1})$ gives the first inequality, and $\sqrt{\varepsilon_1}\ge0$ gives the second. The statement includes $\varepsilon_1=0$ and preserves the explicit coefficient of Eq.(119).
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.2 proof, Eqs.(118)–(119), p.30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf

import Definitions.Def_LindbladTolerant_Testing_lower_bound_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix ENNReal

namespace LindbladTolerant.Testing

theorem dephasing_time_arithmetic (eps1 eps2 T gamma0 gamma1 : ℝ)
    (heps1 : 0 ≤ eps1) (heps12 : eps1 < eps2) (hT : 0 ≤ T)
    (hgamma0 : gamma0 = eps1 / Real.sqrt 2)
    (hgamma1 : gamma1 = eps2 / Real.sqrt 2)
    (hsep : (1/3 : ℝ) ≤ poissonTV (gamma0 * T) (gamma1 * T))
    (hhell : poissonTV (gamma0 * T) (gamma1 * T) ≤
      Real.sqrt (1 - Real.exp (-(Real.sqrt (gamma1 * T) - Real.sqrt (gamma0 * T))^2))) :
    lowerConstant * (Real.sqrt eps2 + Real.sqrt eps1)^2 / (eps2-eps1)^2 ≤ T ∧
    lowerConstant * eps2 / (eps2-eps1)^2 ≤ T := by sorry
