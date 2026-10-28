-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_inner_apply_le_sqrt_hsNormSq_mul_readable
-- name    : FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:12.819494+00:00
-- url     : https://prove2.me/theorems/9a0d0118-09fb-42ba-8956-a35ad70bd1c0
-- title:
--   Hilbert–Schmidt Cauchy–Schwarz Bound
-- statement:
--   This statement gives the Cauchy–Schwarz inequality for the Hilbert–Schmidt pairing.
--
--   Let M and N be continuous linear endomorphisms of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let $(e_j)$ be the canonical orthonormal basis. Then
--
--   $$\sum_j\langle Me_j,Ne_j\rangle
--   \leq\sqrt{\|M\|_{HS}^2}\,\sqrt{\|N\|_{HS}^2}.$$
--
--   This is the basis-coordinate form of Cauchy–Schwarz for Hilbert–Schmidt operators.
--
--   **Formalization Note** The square roots are real square roots of the nonnegative quantities `hsNormSq M` and `hsNormSq N`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_inner_apply_le_sqrt_hsNormSq_mul (M N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
--       ∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j), N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
--         Real.sqrt (hsNormSq M) * Real.sqrt (hsNormSq N)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34).
--
--   Previous: [`opNorm_sq_le_hsNormSq`](https://prove2.me/theorems/4e1eeade-d7a1-4e5a-8b0a-e8fcba8ae762).
--
--   [Source excerpt, lines 159–161](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L159-L161) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L158-L176 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, declaration `FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt

open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.Analysis.sum_inner_apply_le_sqrt_hsNormSq_mul_readable (M N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∑ j, ⟪M (EuclideanSpace.basisFun (Fin n) ℝ j), N (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ≤
      Real.sqrt (hsNormSq M) * Real.sqrt (hsNormSq N) := by sorry
