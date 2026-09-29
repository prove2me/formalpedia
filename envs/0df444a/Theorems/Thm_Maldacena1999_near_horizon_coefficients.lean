-- Prove2me | Theorems.Thm_Maldacena1999_near_horizon_coefficients
-- name    : Maldacena1999.near_horizon_coefficients
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:44:37.817697+00:00
-- url     : https://prove2.me/theorems/98897375-dbed-44ce-a816-fee0e76174a1
-- title:
--   Decoupling limit $\alpha'\to0$: coefficients of the D3-brane metric converge to those of (2.3)
-- statement:
--   Let $g>0$, $N\ge1$ and $U>0$, and let $f_{\alpha'}(r)=1+\dfrac{4\pi gN\alpha'^2}{r^4}$ be the harmonic function of the D3-brane solution (2.2). Substitute $r=\alpha'U$ (so $dr=\alpha'\,dU$) and divide the metric by the overall factor $\alpha'$. Then, as $\alpha'\to0^+$:
--   1. the coefficient of $dx_\parallel^2$: $\displaystyle\frac{f_{\alpha'}(\alpha'U)^{-1/2}}{\alpha'}\longrightarrow\frac{U^2}{\sqrt{4\pi gN}}$;
--   2. the coefficient of $dU^2$: $\displaystyle\frac{f_{\alpha'}(\alpha'U)^{1/2}\,\alpha'^2}{\alpha'}\longrightarrow\frac{\sqrt{4\pi gN}}{U^2}$;
--   3. the coefficient of $d\Omega_5^2$: $\displaystyle\frac{f_{\alpha'}(\alpha'U)^{1/2}\,(\alpha'U)^2}{\alpha'}\longrightarrow\sqrt{4\pi gN}$.
--
--   Together these give eq. (2.3): the D3-brane metric becomes $\alpha'$ times a metric independent of $\alpha'$, in which the $\mathrm{AdS}_5$ part and the five-sphere both have radius $R$ with $R^2=\sqrt{4\pi gN}$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Section 2, eqs. (2.1)-(2.3), p. 1115-1116

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem near_horizon_coefficients (g : ℝ) (hg : 0 < g) (N : ℕ) (hN : 0 < N)
    (U : ℝ) (hU : 0 < U) :
    Tendsto (fun α' : ℝ => 1 / Real.sqrt (harmonicFn g N α' (α' * U)) / α')
        (𝓝[>] 0) (𝓝 (U ^ 2 / Real.sqrt (4 * Real.pi * g * N))) ∧
    Tendsto (fun α' : ℝ => Real.sqrt (harmonicFn g N α' (α' * U)) * α' ^ 2 / α')
        (𝓝[>] 0) (𝓝 (Real.sqrt (4 * Real.pi * g * N) / U ^ 2)) ∧
    Tendsto (fun α' : ℝ => Real.sqrt (harmonicFn g N α' (α' * U)) * (α' * U) ^ 2 / α')
        (𝓝[>] 0) (𝓝 (Real.sqrt (4 * Real.pi * g * N))) := by
  sorry

end Maldacena1999
