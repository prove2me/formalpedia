-- Prove2me | Theorems.Thm_NicolasBRH_prime_ramp_bound_of_RH
-- name    : NicolasBRH.prime_ramp_bound_of_RH
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T04:22:15.653408+00:00
-- url     : https://prove2.me/theorems/822bb14e-795a-462a-b975-a8534355cdfa
-- title:
--   Under RH, $|G(x)/x|\le\beta x^{-1/2}+\log(2\pi)/x$ for Masullo's corrected prime ramp
-- statement:
--   Let $G(x)=\sum_{n\le x}\Lambda(n)\,(x/n-1)-x(\log x-1-\gamma)$, so that $G(x)/x=\sum_{n\le x}\Lambda(n)/n-\psi(x)/x-\log x+1+\gamma$. Assume the Riemann hypothesis. Then for every real $x\ge 2$,
--   $$\Bigl|\frac{G(x)}{x}\Bigr|\le \beta\,x^{-1/2}+\frac{\log 2\pi}{x},\qquad \beta=2+\gamma-\log 4\pi=\sum_\rho\frac{1}{|\rho|^2}.$$
--   The proof combines Masullo's absolutely convergent explicit formula for the increments of $G(x)/x$ with $\sum_\rho m_\rho/|\rho|^2=\beta$, and identifies the limit $\lim_{x\to\infty}G(x)/x=0$ through the Laurent expansion $-\zeta'/\zeta(s)=1/(s-1)-\gamma+O(s-1)$ and an Abelian argument.
-- source:
--   Masullo explicit formula (MasulloRH.prime_ramp_integrated_explicit_formula); Landau (1909) $\sum 1/|\rho|^2=2+\gamma-\log 4\pi$; classical, cf. Broughan, Equivalents of the Riemann Hypothesis Vol. I, Ch. 5.

import Mathlib

namespace NicolasBRH
theorem prime_ramp_bound_of_RH (hRH : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    |((∑ n ∈ Finset.range (⌊x⌋₊+1), ArithmeticFunction.vonMangoldt n * max (x/(n:ℝ)-1) 0) -
        x*(Real.log x-1-Real.eulerMascheroniConstant)) / x| ≤
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * x ^ (-(1/2:ℝ)) +
        Real.log (2 * Real.pi) / x := by sorry
end NicolasBRH
