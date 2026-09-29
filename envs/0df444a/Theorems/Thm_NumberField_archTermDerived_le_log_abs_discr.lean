-- Prove2me | Theorems.Thm_NumberField_archTermDerived_le_log_abs_discr
-- name    : NumberField.archTermDerived_le_log_abs_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/2dbea469-b4a9-5d23-a9f0-df3bfb385dab
-- title:
--   Odlyzko's explicit-formula discriminant bound, totally complex case
-- statement:
--   Let $K$ be a number field that is totally complex, of degree $n = [K:\mathbb{Q}]$ (the rank of $K$ over $\mathbb{Q}$ as a $\mathbb{Q}$-module), and let $F \colon \mathbb{R} \to \mathbb{R}$ satisfy: $F$ is differentiable; $F$ is even, $F(-x) = F(x)$ for all $x$; $F(0) = 1$; $F \ge 0$ pointwise; there are $c, \varepsilon > 0$ with $|F(x)| \le c\,e^{-(1/2+\varepsilon)|x|}$ for all $x$; for every $\rho \in \mathbb{C}$ with $0 < \operatorname{Re}\rho < 1$ one has $\int_{\mathbb{R}} F(x)\,e^{(\operatorname{Re}\rho - 1/2)x}\cos(x\operatorname{Im}\rho)\,dx \ge 0$; $F$ is of class $C^2$; and there are $c, \varepsilon > 0$ with $|F^{(k)}(x)| \le c\,e^{-(1/2+\varepsilon)|x|}$ for all $x$ and all $k \in \{0,1,2\}$. Then
--   $$n\Bigl(\gamma + \log(4\pi) - \int_0^\infty \frac{1 - F(x)}{e^{x/2} - e^{-x/2}}\,dx\Bigr) - 2\int_0^\infty F(x)\bigl(e^{x/2} + e^{-x/2}\bigr)\,dx + n\log 2 \;\le\; \log\bigl|d_K\bigr|,$$
--   where $\gamma$ is the Euler–Mascheroni constant and $d_K$ is the discriminant of $K$, viewed as a real number.
--
--   This is the Weil–Guinand explicit formula for the Dedekind zeta function of $K$ paired against the kernel $F$, in the form used by Odlyzko and Poitou for lower bounds on discriminants: the prime-ideal contribution and the sum over zeros have been discarded by positivity, so no Riemann hypothesis is involved, the strip-positivity hypothesis on $F$ accounting for zeros off the critical line. It is the analytic input to the numerical bound [`NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank`](thm.html#NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank), and it rests on the functional equation, Hadamard factorisation and logarithmic-derivative expansion of the completed Dedekind zeta function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_archTermDerived_le_log_abs_discr.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.archTermDerived_le_log_abs_discr
    (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (F : ℝ → ℝ)
    (h1 : Differentiable ℝ F) (h2 : ∀ x : ℝ, F (-x) = F x) (h3 : F 0 = 1) (h4 : ∀ x : ℝ, 0 ≤ F x)
    (h5 : ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ x : ℝ, |F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|))
    (h6 : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      0 ≤ ∫ x : ℝ, F x * Real.exp ((ρ.re - 1 / 2) * x) * Real.cos (ρ.im * x))
    (h7 : ContDiff ℝ 2 F)
    (h8 : ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ k : Fin 3, ∀ x : ℝ,
      |iteratedDeriv k F x| ≤ c * Real.exp (-(1 / 2 + ε) * |x|)) :
    ((Module.finrank ℚ K : ℝ) * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
        - ∫ x in Set.Ioi (0 : ℝ), (1 - F x) / (Real.exp (x / 2) - Real.exp (-(x / 2))))
      - 2 * ∫ x in Set.Ioi (0 : ℝ), F x * (Real.exp (x / 2) + Real.exp (-(x / 2))))
      + (Module.finrank ℚ K : ℝ) * Real.log 2 ≤ Real.log |(NumberField.discr K : ℝ)| := by sorry
