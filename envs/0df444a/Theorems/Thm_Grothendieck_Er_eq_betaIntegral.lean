-- Prove2me | Theorems.Thm_Grothendieck_Er_eq_betaIntegral
-- name    : Grothendieck.Er_eq_betaIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:22:45.494933+00:00
-- url     : https://prove2.me/theorems/ef74d848-738d-4352-98c5-75fc0d03d9b7
-- title:
--   The series $E_r$ as a Beta-type integral
-- statement:
--   The paper's function $E_r:[-1,1]\to[-1,1]$ is introduced as a Gaussian rounding expectation and computed in Lemma 2.1 as the hypergeometric series
--
--   $$
--   E_r(t)=C_r\,t\;{}_2F_1\!\Big(\begin{smallmatrix}1/2,\,1/2\\ r/2+1\end{smallmatrix};t^2\Big),\qquad C_r=\frac2r\Big(\frac{\Gamma((r+1)/2)}{\Gamma(r/2)}\Big)^2 .
--   $$
--
--   This node records its Euler Beta-integral form. For every integer $r\ge1$ and every real $t$ with $|t|<1$,
--
--   $$
--   E_r(t)=\frac{\Gamma\big(\tfrac{r+1}{2}\big)}{\sqrt\pi\,\Gamma\big(\tfrac r2\big)}\;t\int_0^1 u^{-1/2}(1-u)^{\frac{r-1}{2}}(1-t^2u)^{-1/2}\,du .
--   $$
--
--   The identity is Euler's Beta-integral representation of ${}_2F_1$ at the parameters $(1/2,1/2;r/2+1)$, with $\Gamma(r/2+1)=(r/2)\Gamma(r/2)$ accounting for the constant. The paper reaches the same formula through spherical coordinates and Bessel functions; the proof here avoids both — it expands $(1-x)^{-1/2}$ through the Gamma integral and dominated convergence, integrates termwise on $[0,1]$, evaluates each term as a Beta moment, and matches coefficients against the definition of $E_r$. This is the analytic input of the Laplace-transform route to Lemma 2.1.
--
--   **Formalization Note** $\int_0^1\ldots$ is the interval integral `∫ u in (0 : ℝ)..1, ...` and $u^{-1/2}$ is the real power `u ^ (-(1/2) : ℝ)`; both exponents are integrable at the endpoints because $-1/2>-1$.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

open MeasureTheory intervalIntegral
open scoped BigOperators Real

namespace Grothendieck

/-- **The Beta-integral representation of the paper's series.** For `r ≥ 1` and `|t| < 1`, the
hypergeometric series `E_r` of Definition 2.1 equals a Beta-type integral, with no Bessel function
and no Euler transformation in the proof. -/
theorem Er_eq_betaIntegral (r : ℕ) (hr : 1 ≤ r) {t : ℝ} (ht : |t| < 1) :
    Er r t = Real.Gamma (((r : ℝ) + 1) / 2)
        / (Real.sqrt Real.pi * Real.Gamma ((r : ℝ) / 2)) *
      (t * ∫ u in (0 : ℝ)..1, u ^ (-(1/2) : ℝ) * (1 - u) ^ (((r : ℝ) - 1) / 2) *
        (1 - t ^ 2 * u) ^ (-(1/2) : ℝ)) := by sorry

end Grothendieck
