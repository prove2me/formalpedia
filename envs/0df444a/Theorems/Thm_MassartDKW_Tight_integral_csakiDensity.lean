-- Prove2me | Theorems.Thm_MassartDKW_Tight_integral_csakiDensity
-- name    : MassartDKW.Tight.integral_csakiDensity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:49.660537+00:00
-- url     : https://prove2.me/theorems/a2b1618c-6d44-4d0e-93f2-ed295e3871cf
-- title:
--   (2.4), p. 1272 — ∫₀¹ f_λ(s) ds = exp(−2λ²)
-- statement:
--   For every $\lambda>0$, Csáki's density $f_\lambda(s)=\frac{\lambda}{\sqrt{2\pi}}s^{-3/2}(1-s)^{-1/2}\exp\bigl(-\frac{\lambda^2}{2s(1-s)}\bigr)$ satisfies
--   $$\int_0^1 f_\lambda(s)\,ds=\exp(-2\lambda^2).$$
--
--   Probabilistically, $f_\lambda$ is the density of the first passage time of a Brownian bridge at level $\lambda$, and the identity says that this level is reached with probability $\exp(-2\lambda^2)$. It is the limit against which the exact sum (2.3) is compared, and it gives Lemma 4(i).
--
--   **Formalization Note** The statement is the closed-form integral; no Brownian bridge is formalized. The integrand is integrable on $]0,1[$ (the exponential factor kills both endpoint singularities), so the interval integral is the genuine one. `l` stands for $\lambda$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1272, (2.4)

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem integral_csakiDensity (l : ℝ) (hl : 0 < l) :
    ∫ s in (0 : ℝ)..1, csakiDensity l s = Real.exp (-2 * l ^ 2) := by sorry

end MassartDKW.Tight
