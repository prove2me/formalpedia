-- Prove2me | Theorems.Thm_MuirheadMST_wishart_density
-- name    : MuirheadMST.wishart_density
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T17:38:00.647792+00:00
-- url     : https://prove2.me/theorems/8da08678-7e5d-5d40-99b8-1527478ff814
-- title:
--   Theorem 3.2.1: the density of the Wishart distribution $W_m(n,\Sigma)$
-- statement:
--   Let $1\le m\le n$ and let $\Sigma$ be a positive definite $m\times m$ matrix. If $A\sim W_m(n,\Sigma)$, that is, $A=Z^{\mathsf T}Z$ for an $n\times m$ matrix $Z$ with independent $N_m(0,\Sigma)$ rows, then $A$ has density
--
--   $$
--   \frac{1}{2^{mn/2}\,\Gamma_m(n/2)\,(\det\Sigma)^{n/2}}\,\operatorname{etr}\Big(-\frac12\Sigma^{-1}A\Big)\,(\det A)^{(n-m-1)/2}
--   $$
--
--   on positive definite matrices $A$, and density $0$ elsewhere, with respect to Lebesgue measure $(dA)=\prod_{i\le j}dA_{ij}$ on symmetric matrices. Here $\operatorname{etr}(X)=e^{\operatorname{tr}X}$ and $\Gamma_m$ is the multivariate gamma function.
--
--   This theorem turns probabilities about Wishart matrices into integrals over the cone of positive definite matrices; it is the starting point for the distribution of the latent roots.
--
--   **Formalization Note** The statement is an equality of measures on arrays `Fin m → Fin m → ℝ`; `symVolume m` is $(dA)$, supported on symmetric arrays. $m=0$ is allowed and trivial.
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982 (reprinted 2005, same pagination), https://doi.org/10.1002/9780470316559, §3.2, Theorem 3.2.1, p. 85

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory

namespace MuirheadMST

open scoped Classical in
theorem wishart_density (m n : ℕ) (hmn : m ≤ n) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef) :
    wishart m n S = (symVolume m).withDensity fun A => ENNReal.ofReal
      (if (Matrix.of A).PosDef then
        (2 ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2) * S.det ^ ((n : ℝ) / 2))⁻¹ *
          Real.exp (-(1 / 2) * (S⁻¹ * Matrix.of A).trace) *
          (Matrix.of A).det ^ (((n : ℝ) - m - 1) / 2)
      else 0) := by sorry

end MuirheadMST
