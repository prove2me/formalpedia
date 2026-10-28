-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_spectral_geometry_readable
-- name    : FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:22.343397+00:00
-- url     : https://prove2.me/theorems/a896bf49-4875-4093-8aae-c4e196200010
-- title:
--   Spectral Geometry of an Invertible Symmetric Matrix
-- statement:
--   This is an auxiliary finite-dimensional package of spectral facts for an invertible symmetric matrix.
--
--   Let $n\in\mathbb N$ and let $M$ be a symmetric real matrix on $\operatorname{Fin}(n)$. Assume that $M$ is a unit matrix. Define
--
--   $$
--   B=\operatorname{CFC.sqrt}(M^2),\qquad
--   S=\operatorname{CFC.sqrt}(B),\qquad
--   Q=\operatorname{cfc}(x\mapsto\operatorname{sign}(x))(M).
--   $$
--
--   Then:
--
--   1. $B$ and $S$ are positive semidefinite;
--   2. $Q$ is symmetric;
--   3. $B^2=M^2$, $S^2=B$, and $SQS=M$;
--   4. $Q^2=I$ and $S$ is a unit matrix;
--   5. the continuous linear map induced by $Q$ is self-adjoint;
--   6. there exists a continuous linear equivalence $e$ of $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$ whose continuous linear map is the map induced by $S$, and this map is self-adjoint.
--
--   This packages the matrix identities and operator-theoretic properties needed when passing from spectral matrices to Euclidean-space maps.
--
--   **Formalization Note** The conclusion is valid for every $n$, including $n=0$; the Euclidean space is specifically `EuclideanSpace ℝ (Fin n)`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 700000 in
--   theorem symmetric_matrix_spectral_geometry {n : ℕ}
--       (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) :
--       let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
--       let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
--       let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
--       B.PosSemidef ∧ S.PosSemidef ∧ Q.IsSymm ∧ B*B=M*M ∧ S*S=B ∧ S*Q*S=M ∧ Q*Q=1 ∧ IsUnit S ∧
--       IsSelfAdjoint (Matrix.toEuclideanLin Q).toContinuousLinearMap ∧
--       ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
--         e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap ∧
--         IsSelfAdjoint e.toContinuousLinearMap
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8).
--
--   Supporting theorems: [`symmetric_matrix_sign_factorization`](https://prove2.me/theorems/dc2e7bc6-783c-47b2-ab0e-99d975ec6a82), [`symmetric_matrix_sqrt_real_cfc_bridge`](https://prove2.me/theorems/55e7d3a2-5447-43f2-ad4d-6d412da05abe).
--
--   Previous: [`symmetric_jordan_decomposition`](https://prove2.me/theorems/a088e571-4bf9-4eb8-9d83-6d45e8be135b) · Next: [`exists_symmetric_isUnit_matrix_sequence`](https://prove2.me/theorems/2457a68a-10fc-4205-94a6-4898596c7fa3).
--
--   [Source excerpt, lines 349–359](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L349-L359) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L349-L404 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign

open scoped MatrixOrder
set_option maxHeartbeats 700000

theorem FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_readable {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    B.PosSemidef ∧ S.PosSemidef ∧ Q.IsSymm ∧ B*B=M*M ∧ S*S=B ∧ S*Q*S=M ∧ Q*Q=1 ∧ IsUnit S ∧
    IsSelfAdjoint (Matrix.toEuclideanLin Q).toContinuousLinearMap ∧
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap ∧
      IsSelfAdjoint e.toContinuousLinearMap := by sorry
