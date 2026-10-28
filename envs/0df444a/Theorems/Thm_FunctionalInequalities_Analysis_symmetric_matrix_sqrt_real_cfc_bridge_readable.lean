-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sqrt_real_cfc_bridge_readable
-- name    : FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:08.565206+00:00
-- url     : https://prove2.me/theorems/55e7d3a2-5447-43f2-ad4d-6d412da05abe
-- title:
--   Real Continuous-Functional-Calculus Square-Root Bridge
-- statement:
--   This is an auxiliary bridge between the matrix square-root construction `CFC.sqrt` and the real continuous functional calculus.
--
--   Let $\iota$ be a finite index type with decidable equality, and let $M$ be a real symmetric matrix indexed by $\iota$. Then:
--
--   1. $M^2$ is positive semidefinite;
--   2. its matrix square root agrees with the real functional-calculus expression;
--   3. $\operatorname{CFC.sqrt}(M^2)$ is positive semidefinite;
--   4. the square root of this matrix again agrees with the corresponding real functional-calculus expression.
--
--   Explicitly,
--
--   $$
--   0\le M^2,\qquad
--   \operatorname{CFC.sqrt}(M^2)=\operatorname{cfc}(x\mapsto\sqrt{x})(M^2),
--   $$
--
--   and
--
--   $$
--   0\le \operatorname{CFC.sqrt}(M^2),\qquad
--   \operatorname{CFC.sqrt}(\operatorname{CFC.sqrt}(M^2))
--   =\operatorname{cfc}(x\mapsto\sqrt{x})(\operatorname{CFC.sqrt}(M^2)).
--   $$
--
--   The result supplies the square-root identities needed for the spectral sign factorization.
--
--   **Formalization Note** Positivity is expressed by matrix order, and no positivity assumption on $M$ itself is required.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem symmetric_matrix_sqrt_real_cfc_bridge
--       (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
--       0 ≤ M * M ∧
--         CFC.sqrt (M * M) = cfc (fun x : ℝ => Real.sqrt x) (M * M) ∧
--         0 ≤ CFC.sqrt (M * M) ∧
--         CFC.sqrt (CFC.sqrt (M * M)) =
--           cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8).
--
--   Next: [`symmetric_matrix_sign_factorization`](https://prove2.me/theorems/dc2e7bc6-783c-47b2-ab0e-99d975ec6a82).
--
--   [Source excerpt, lines 43–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L43-L49) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L40-L64 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign

open scoped MatrixOrder
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_readable
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    0 ≤ M * M ∧
      CFC.sqrt (M * M) = cfc (fun x : ℝ => Real.sqrt x) (M * M) ∧
      0 ≤ CFC.sqrt (M * M) ∧
      CFC.sqrt (CFC.sqrt (M * M)) =
        cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) := by sorry
