-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_symmetric_isUnit_matrix_sequence_readable
-- name    : FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:32.235258+00:00
-- url     : https://prove2.me/theorems/2457a68a-10fc-4205-94a6-4898596c7fa3
-- title:
--   Symmetric Invertible Approximation of a Symmetric Matrix
-- statement:
--   This is a finite-dimensional matrix approximation lemma.
--
--   Let $\iota$ be a finite type with decidable equality, and let $A$ be a real $\iota\times\iota$ matrix satisfying $A^{\mathsf T}=A$. Then there exists a sequence of matrices $(A_k)_{k\in\mathbb N}$ such that every $A_k$ is symmetric and invertible, and
--
--   $$
--   A_k\longrightarrow A
--   $$
--
--   as $k\to\infty$ in the matrix topology. The result supplies invertible symmetric approximants without requiring $A$ itself to be invertible.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   set_option maxHeartbeats 300000 in
--   theorem exists_symmetric_isUnit_matrix_sequence {ι : Type*} [Fintype ι] [DecidableEq ι]
--       (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
--       ∃ seq : ℕ → Matrix ι ι ℝ,
--         (∀ k, (seq k).IsSymm ∧ IsUnit (seq k)) ∧ Tendsto seq atTop (𝓝 A)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8).
--
--   Previous: [`symmetric_matrix_spectral_geometry`](https://prove2.me/theorems/a896bf49-4875-4093-8aae-c4e196200010).
--
--   [Source excerpt, lines 416–420](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L416-L420) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L416-L435 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign

open Matrix Filter Set
open scoped Topology
set_option maxHeartbeats 300000

theorem FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence_readable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ∃ seq : ℕ → Matrix ι ι ℝ,
      (∀ k, (seq k).IsSymm ∧ IsUnit (seq k)) ∧ Tendsto seq atTop (𝓝 A) := by sorry
