-- Prove2me | Theorems.Thm_MuirheadMST_multivariateGamma_eq_integral
-- name    : MuirheadMST.multivariateGamma_eq_integral
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T17:37:21.434397+00:00
-- url     : https://prove2.me/theorems/b3bfae5f-9799-5998-8943-aba39c96ef38
-- title:
--   Theorem 2.1.12: the multivariate gamma integral $\int_{A>0}\operatorname{etr}(-A)(\det A)^{a-(m+1)/2}(dA)=\Gamma_m(a)$
-- statement:
--   Let $m\ge0$ and let $a$ be a real number with $a>(m-1)/2$. Then
--
--   $$
--   \int_{A>0}\operatorname{etr}(-A)\,(\det A)^{a-(m+1)/2}\,(dA)=\pi^{m(m-1)/4}\prod_{i=1}^m\Gamma\Big(a-\frac{i-1}{2}\Big)=\Gamma_m(a),
--   $$
--
--   where the integral runs over positive definite $m\times m$ matrices, $(dA)=\prod_{i\le j}dA_{ij}$ is Lebesgue measure on symmetric matrices, and $\operatorname{etr}(X)=e^{\operatorname{tr}X}$.
--
--   This integral is the normalizing constant of the Wishart density and, more generally, of every gamma-type density on the cone of positive definite matrices.
--
--   **Formalization Note** The source allows complex $a$ with $\operatorname{Re}a>(m-1)/2$; this statement is the case of real $a$. The integral is a Lebesgue integral with values in $[0,\infty]$, so the statement includes its finiteness.
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982 (reprinted 2005, same pagination), https://doi.org/10.1002/9780470316559, §2.1.2, Theorem 2.1.12, pp. 62-63 (stated there for complex a with Re a > (m-1)/2; this is the real case)

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory

namespace MuirheadMST

open scoped Classical in
theorem multivariateGamma_eq_integral (m : ℕ) (a : ℝ) (ha : ((m : ℝ) - 1) / 2 < a) :
    ∫⁻ A, ENNReal.ofReal
      (if (Matrix.of A).PosDef then
        Real.exp (-(Matrix.of A).trace) * (Matrix.of A).det ^ (a - ((m : ℝ) + 1) / 2)
      else 0) ∂(symVolume m) = ENNReal.ofReal (multivariateGamma m a) := by sorry

end MuirheadMST
