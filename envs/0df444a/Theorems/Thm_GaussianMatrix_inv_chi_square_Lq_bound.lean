-- Prove2me | Theorems.Thm_GaussianMatrix_inv_chi_square_Lq_bound
-- name    : GaussianMatrix.inv_chi_square_Lq_bound
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T04:59:01.240497+00:00
-- url     : https://prove2.me/theorems/722f3d91-4c01-4e3f-be14-ba4bb2551e54
-- title:
--   $L^q$ norm of a reciprocal chi-square: $\mathbb{E}[\Xi^{-q}] < (3/d)^q$ for $q=(d-1)/2$, $d \ge 5$ (HMT Lemma A.10)
-- statement:
--   Let $d \ge 5$ and let $\Xi = \sum_{j=1}^d x_j^2$ with $x \sim \mathcal{N}(0, I_d)$, a chi-square variable with $d$ degrees of freedom. Put $q = (d-1)/2$. Then $\Xi^{-q}$ is integrable and
--
--   $$\mathbb{E}\big[\Xi^{-q}\big] \;<\; \Big(\frac{3}{d}\Big)^{q}, \qquad\text{i.e.}\qquad \mathbb{E}_q\big(\Xi^{-1}\big) = \big(\mathbb{E}\,\Xi^{-q}\big)^{1/q} < \frac{3}{d}.$$
--
--   By the negative-moment formula, $\mathbb{E}[\Xi^{-q}] = \Gamma(1/2)/(2^q\Gamma(d/2)) = \sqrt{\pi}/(2^q\Gamma(d/2))$, so the claim is the Gamma-function inequality $\sqrt{\pi}\, d^{\,q} < 6^{q}\,\Gamma(d/2)$.
--
--   This is the key moment estimate in the tail bound for $\|G^\dagger\|_F^2$: each diagonal entry of $(GG^\top)^{-1}$ for an $r\times k$ Gaussian $G$ is distributed as $1/\chi^2_{k-r+1}$, and the bound with $d = k-r+1$ and $q = (k-r)/2$ controls its $L^q$ norm.
--
--   **Formalization Note.** The power is the real power `Real.rpow` applied to the nonnegative quantity $(\sum_j x_j^2)^{-1}$ (with $0^{-1}=0$). HMT state the lemma for $2 \le q \le (d-1)/2$ and reduce it to the endpoint $q=(d-1)/2$ by Hölder's inequality; only the endpoint case is formalized here.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, Finding structure with randomness: Probabilistic algorithms for constructing approximate matrix decompositions, SIAM Review 53(2) (2011), 217–288 (arXiv:0909.4061), Lemma A.10 (arXiv version p. 67): for $k \ge 5$ and $2 \le q \le (k-1)/2$, $\mathbb{E}_q(\Xi^{-1}) < 3/k$; the proof there establishes exactly the endpoint case $q = (k-1)/2$ stated here.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inv_chi_square_Lq_bound {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2))
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      < (3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2) := by sorry

end GaussianMatrix
