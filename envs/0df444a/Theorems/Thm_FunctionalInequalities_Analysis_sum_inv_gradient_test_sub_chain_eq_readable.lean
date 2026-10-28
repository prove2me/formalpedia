-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_inv_gradient_test_sub_chain_eq_readable
-- name    : FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:46.085001+00:00
-- url     : https://prove2.me/theorems/7266b246-03c7-419d-a30f-6d99183cc1fc
-- title:
--   Finite Inverse-Hessian Cancellation Identity
-- statement:
--   This is a finite-dimensional algebraic identity supporting the weak inverse-Hessian calculation.
--
--   Let $A,B$ be real $n\times n$ matrices. Assume $A$ is Hermitian and $\det A$ is a unit, so that $A^{-1}$ is available. For real $a$ and vectors $b,p,q,r:\operatorname{Fin}(n)\to\mathbb R$, the difference between the two displayed inverse-matrix contractions equals
--   $$\sum_{i,j}(A^{-1})_{ij}b_i r_j
--   +a\left(\operatorname{tr}(A^{-1}B)-\sum_iq_i r_i\right).$$
--
--   More explicitly, the left side is
--   $$\sum_{i,j}(A^{-1})_{ij}(b_jr_i-ap_jr_i+aB_{ji})
--   -\sum_{i,j}(A^{-1})_{ij}\left(-p_j+\sum_kA_{jk}q_k\right)(ar_i).$$
--
--   The lemma contains no analytic assumptions; it is a reusable matrix-and-finite-sum cancellation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem sum_inv_gradient_test_sub_chain_eq {n : ℕ}
--       (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
--       (a : ℝ) (b p q r : Fin n → ℝ) :
--       (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
--         (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
--         (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
--           a * ((A⁻¹ * B).trace - ∑ i, q i * r i)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak`](https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8).
--
--   Previous: [`ae_fderiv_mongeAmpere_exponent`](https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529) · Next: [`smooth_test_derivative`](https://prove2.me/theorems/a020d053-5b2e-45e7-bfaf-a25b6c53786c).
--
--   [Source excerpt, lines 310–316](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L310-L316) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L308-L369 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak.0.FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak

theorem FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_readable {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : ℝ) (b p q r : Fin n → ℝ) :
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
      (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
      (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
        a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by sorry
