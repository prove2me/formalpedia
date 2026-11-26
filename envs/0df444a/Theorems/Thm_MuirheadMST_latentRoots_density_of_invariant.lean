-- Prove2me | Theorems.Thm_MuirheadMST_latentRoots_density_of_invariant
-- name    : MuirheadMST.latentRoots_density_of_invariant
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T17:38:31.691911+00:00
-- url     : https://prove2.me/theorems/0921697f-86e8-4214-8c32-fbcbb6bfcb1d
-- title:
--   Theorem 3.2.17 (orthogonally invariant case): latent roots of a random positive definite matrix
-- statement:
--   Let $A$ be a random $m\times m$ positive definite matrix whose law has density $f$ with respect to Lebesgue measure $(dA)=\prod_{i\le j}dA_{ij}$ on symmetric matrices, and suppose $f$ is orthogonally invariant: $f(HAH^{\mathsf T})=f(A)$ for every orthogonal $H$. Then the latent roots $l_1>l_2>\dots>l_m>0$ of $A$ have joint density
--
--   $$
--   \frac{\pi^{m^2/2}}{\Gamma_m(m/2)}\;f\big(\operatorname{diag}(l_1,\dots,l_m)\big)\prod_{i<j}(l_i-l_j)
--   $$
--
--   on $\{l_1>\dots>l_m>0\}$, and density $0$ elsewhere.
--
--   Theorem 3.2.17 of the source holds for every density $f$, with $f(\operatorname{diag}(l))$ replaced by $\int_{O(m)} f(HLH^{\mathsf T})\,(dH)$ over the normalized Haar measure on the orthogonal group $O(m)$. For orthogonally invariant $f$ this integral equals $f(L)$, so the statement here is that theorem in the invariant case. Its proof rests on the Jacobian of the spectral decomposition $A=HLH^{\mathsf T}$, derived in the proof of Theorem 3.2.17 (pp. 104 to 105).
--
--   **Formalization Note** $f$ takes values in $[0,\infty]$ and need not be normalized; it is required to vanish off positive definite matrices, as in the source. The latent roots are the eigenvalues in decreasing order (`latentRoots`).
-- source:
--   R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley, 1982 (reprinted 2005, same pagination), https://doi.org/10.1002/9780470316559, §3.2.5 'The Latent Roots of a Wishart Matrix', Theorem 3.2.17, p. 104 (the case of an orthogonally invariant density f, where the integral over O(m) reduces to f(L)); the Jacobian of A = HLH' is derived in its proof, pp. 104-105

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory

namespace MuirheadMST

open scoped Classical in
theorem latentRoots_density_of_invariant (m : ℕ) (f : (Fin m → Fin m → ℝ) → ENNReal)
    (hf : Measurable f) (hpd : ∀ A, ¬(Matrix.of A).PosDef → f A = 0)
    (hinv : ∀ H ∈ Matrix.orthogonalGroup (Fin m) ℝ, ∀ A,
      f (Matrix.of.symm (H * Matrix.of A * H.transpose)) = f A) :
    ((symVolume m).withDensity f).map latentRoots =
      (volume : Measure (Fin m → ℝ)).withDensity fun l =>
        if StrictAnti l ∧ ∀ i, 0 < l i then
          ENNReal.ofReal (Real.pi ^ ((m : ℝ) ^ 2 / 2) / multivariateGamma m ((m : ℝ) / 2) *
            vandermondeProd l) * f (diagArray l)
        else 0 := by sorry

end MuirheadMST
