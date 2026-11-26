-- Prove2me | Theorems.Thm_MuirheadMST_wishart_latentRoots_density
-- name    : MuirheadMST.wishart_latentRoots_density
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T17:38:53.340853+00:00
-- url     : https://prove2.me/theorems/5fc78d46-3990-53f8-ad45-5c2bd3f98301
-- title:
--   Corollary 3.2.19 ($\Sigma=\lambda I_m$): the joint density of the latent roots of $W_m(n,\lambda I_m)$
-- statement:
--   Let $1\le m\le n$ and $\lambda>0$. If $A\sim W_m(n,\lambda I_m)$, the latent roots $l_1>l_2>\dots>l_m>0$ of $A$ have joint density
--
--   $$
--   \frac{\pi^{m^2/2}}{(2\lambda)^{mn/2}\,\Gamma_m(n/2)\,\Gamma_m(m/2)}\;\exp\Big(-\frac{1}{2\lambda}\sum_{i=1}^m l_i\Big)\prod_{i=1}^m l_i^{(n-m-1)/2}\prod_{i<j}(l_i-l_j)
--   $$
--
--   on $\{l_1>\dots>l_m>0\}$, and density $0$ elsewhere, with respect to Lebesgue measure on $\mathbb R^m$.
--
--   This is the eigenvalue law of the real Wishart matrix, known in random matrix theory as the Laguerre orthogonal ensemble. It underlies the exact distributions of the extreme eigenvalues and condition numbers of Gaussian matrices.
--
--   **Formalization Note** The latent roots are the eigenvalues of $A$ in decreasing order (`latentRoots`); the statement is an equality of measures on $\mathbb R^m$.
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982 (reprinted 2005, same pagination), https://doi.org/10.1002/9780470316559, §3.2.5 'The Latent Roots of a Wishart Matrix', Corollary 3.2.19 (Σ = λI_m), the special case of Theorem 3.2.18. Citation status: the number 3.2.19 is confirmed by one citing paper (arXiv:2103.05574, which cites it for the identity scale matrix); the Σ = λI_m form follows the published derivation of this exact formula in Bejan's notes on the largest eigenvalue of real Wishart matrices (http://users.stat.umn.edu/~jiang040/downloadpapers/largesteigen/largesteigen.pdf). The formula itself is independently confirmed by Edelman (1989, Lemma 3.2 with Theorem 3.2) and Edelman and Rao (2005, §4.5) for λ = 1.

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory

namespace MuirheadMST

open scoped Classical in
theorem wishart_latentRoots_density (m n : ℕ) (hmn : m ≤ n) (lam : ℝ) (hlam : 0 < lam) :
    (wishart m n (lam • (1 : Matrix (Fin m) (Fin m) ℝ))).map latentRoots =
      (volume : Measure (Fin m → ℝ)).withDensity fun l => ENNReal.ofReal
        (if StrictAnti l ∧ ∀ i, 0 < l i then
          Real.pi ^ ((m : ℝ) ^ 2 / 2) /
              ((2 * lam) ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2) *
                multivariateGamma m ((m : ℝ) / 2)) *
            Real.exp (-(∑ i, l i) / (2 * lam)) * (∏ i, l i ^ (((n : ℝ) - m - 1) / 2)) *
            vandermondeProd l
        else 0) := by sorry

end MuirheadMST
