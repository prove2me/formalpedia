-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sign_factorization_readable
-- name    : FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:08.900739+00:00
-- url     : https://prove2.me/theorems/dc2e7bc6-783c-47b2-ab0e-99d975ec6a82
-- title:
--   Spectral Sign Factorization
-- statement:
--   This is an auxiliary spectral factorization for a real symmetric matrix.
--
--   Let $\iota$ be a finite index type with decidable equality, and let $M$ be a symmetric real matrix indexed by $\iota$. Define
--
--   $$
--   A=\operatorname{CFC.sqrt}(M^2),\qquad
--   S=\operatorname{CFC.sqrt}(A),\qquad
--   \operatorname{Sign}(M)=\operatorname{cfc}(x\mapsto\operatorname{sign}(x))(M).
--   $$
--
--   Then
--
--   $$
--   S^2=A,
--   $$
--
--   and
--
--   $$
--   S\,\operatorname{Sign}(M)\,S=M.
--   $$
--
--   Moreover, if $M$ is a unit matrix, then
--
--   $$
--   \operatorname{Sign}(M)^2=I.
--   $$
--
--   The factorization isolates the sign component of a possibly singular or indefinite symmetric matrix and is reusable in arguments involving square-root weights.
--
--   **Formalization Note** The definitions correspond to `CFC.sqrt` and `cfc`; the sign-square identity is asserted only under `IsUnit M`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem symmetric_matrix_sign_factorization
--       (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
--       let AbsM : Matrix ι ι ℝ := CFC.sqrt (M * M)
--       let S : Matrix ι ι ℝ := CFC.sqrt AbsM
--       let SignM : Matrix ι ι ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
--       S * S = AbsM ∧ S * SignM * S = M ∧
--         (IsUnit M → SignM * SignM = 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8).
--
--   Supporting theorems: [`symmetric_matrix_sqrt_real_cfc_bridge`](https://prove2.me/theorems/55e7d3a2-5447-43f2-ad4d-6d412da05abe).
--
--   Previous: [`symmetric_matrix_sqrt_real_cfc_bridge`](https://prove2.me/theorems/55e7d3a2-5447-43f2-ad4d-6d412da05abe) · Next: [`symmetric_jordan_decomposition`](https://prove2.me/theorems/a088e571-4bf9-4eb8-9d83-6d45e8be135b).
--
--   [Source excerpt, lines 108–114](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L108-L114) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L105-L232 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign

open scoped MatrixOrder
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization_readable
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    let AbsM : Matrix ι ι ℝ := CFC.sqrt (M * M)
    let S : Matrix ι ι ℝ := CFC.sqrt AbsM
    let SignM : Matrix ι ι ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    S * S = AbsM ∧ S * SignM * S = M ∧
      (IsUnit M → SignM * SignM = 1) := by sorry
