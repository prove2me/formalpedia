-- Prove2me | Theorems.Thm_Grothendieck_constant_bookkeeping
-- name    : Grothendieck.constant_bookkeeping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T05:44:24.913417+00:00
-- url     : https://prove2.me/theorems/6e4e0928-817c-4cdd-931e-fda17baa8bcf
-- title:
--   The constant bookkeeping of Lemma 2.1: $\frac{2r\tau}{\pi}\cdot\frac12\Gamma(\tfrac12)\Gamma(M-\tfrac12)/\Gamma(M)\cdot\frac12=\tau\Gamma(\tfrac{r+1}{2})/(\sqrt\pi\Gamma(\tfrac r2))$
-- statement:
--   For every $r\ge1$ and real $\tau$, with $M=\frac{r+2}{2}$,
--   $$\frac{2r\tau}{\pi}\cdot\frac12\frac{\Gamma(\frac12)\Gamma(M-\frac12)}{\Gamma(M)}\cdot\frac12
--   =\frac{\tau\,\Gamma(\frac{r+1}{2})}{\sqrt\pi\,\Gamma(\frac r2)}.$$
--   This is the arithmetic of Lemma 2.1's final step, isolated so that it can be checked once. The left side is the constant the chain produces: $2r\tau/\pi$ from the substitutions, $\frac12\Gamma(\frac12)\Gamma(M-\frac12)/\Gamma(M)$ from the $p$-integral, and $\frac12$ from the $q^2=x/(1-x)$ substitution. The right side is the constant in the paper's $E_r$, whose defining series is $E_r(t)=\frac{\Gamma((r+1)/2)}{\sqrt\pi\Gamma(r/2)}t\int_0^1\frac{u^{-1/2}(1-u)^{(r-1)/2}}{\sqrt{1-\tau^2u}}du$.
--
--   The identity holds because $\Gamma(\frac{r+2}{2})=\frac r2\Gamma(\frac r2)$ (from $\Gamma(x+1)=x\Gamma(x)$) cancels the factor $r$, and $\Gamma(\frac12)=\sqrt\pi$ turns $\pi$ into $\sqrt\pi$. It also records $\Gamma(\frac{r+2}{2})=\frac r2\Gamma(\frac r2)$ as a separate lemma, which is what several other steps need.
--
--   **Formalization Note** A supporting identity; it contains no analysis, only Gamma arithmetic.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - the constant comparison closing Lemma 2.1 (equation (2.1) against the substituted integral).

import Mathlib

open scoped BigOperators Real

namespace Grothendieck

/-- **The constant bookkeeping of Lemma 2.1.** With `M = (r+2)/2`, the prefactor
`2rτ/π · ½Γ(½)Γ(M-½)/Γ(M) · ½` equals `τ·Γ((r+1)/2)/(√π·Γ(r/2))`, the constant in `E_r`. -/
theorem constant_bookkeeping (r : ℕ) (hr : 1 ≤ r) (τ : ℝ) :
    2 * (r : ℝ) * τ * Real.pi⁻¹ *
        (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
          Real.Gamma (((r : ℝ) + 2) / 2)) * (1 / 2)
      = τ * Real.Gamma (((r : ℝ) + 1) / 2) / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) := by sorry

end Grothendieck
