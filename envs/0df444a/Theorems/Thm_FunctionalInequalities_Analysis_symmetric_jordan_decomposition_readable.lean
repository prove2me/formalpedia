-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_jordan_decomposition_readable
-- name    : FunctionalInequalities.Analysis.symmetric_jordan_decomposition_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:09.071178+00:00
-- url     : https://prove2.me/theorems/a088e571-4bf9-4eb8-9d83-6d45e8be135b
-- title:
--   Jordan Decomposition of a Symmetric Matrix
-- statement:
--   This formalizes an auxiliary spectral decomposition for real symmetric matrices.
--
--   Let $\iota$ be a finite index type, with decidable equality, and let $B$ be a real matrix indexed by $\iota$. Assume that $B$ is symmetric. Then there exist real matrices $P$ and $N$ such that:
--
--   1. $P$ and $N$ are positive semidefinite;
--   2. $B=P-N$;
--   3. $PN=0$ and $NP=0$;
--   4. the squared trace decomposes as
--
--   $$
--   \operatorname{tr}(B^2)=\operatorname{tr}(P^2)+\operatorname{tr}(N^2).
--   $$
--
--   This is the matrix Jordan decomposition used to extend trace-energy estimates from positive semidefinite matrices to arbitrary symmetric matrices.
--
--   **Formalization Note** The matrices are constructed through the real continuous functional calculus `cfc`; the result includes the empty finite index type.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem symmetric_jordan_decomposition (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
--       ∃ P N : Matrix ι ι ℝ,
--         P.PosSemidef ∧ N.PosSemidef ∧ B = P - N ∧
--         P * N = 0 ∧ N * P = 0 ∧
--         (B * B).trace = (P * P).trace + (N * N).trace
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8).
--
--   Supporting theorems: [`cfc_eq_mul_diagonal_mul`](https://prove2.me/theorems/09ddc3bd-8df9-4276-88d0-412e386bc91f).
--
--   Previous: [`symmetric_matrix_sign_factorization`](https://prove2.me/theorems/dc2e7bc6-783c-47b2-ab0e-99d975ec6a82) · Next: [`symmetric_matrix_spectral_geometry`](https://prove2.me/theorems/a896bf49-4875-4093-8aae-c4e196200010).
--
--   [Source excerpt, lines 261–265](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L261-L265) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L258-L320 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_jordan_decomposition`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_jordan_decomposition_readable (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    ∃ P N : Matrix ι ι ℝ,
      P.PosSemidef ∧ N.PosSemidef ∧ B = P - N ∧
      P * N = 0 ∧ N * P = 0 ∧
      (B * B).trace = (P * P).trace + (N * N).trace := by sorry
