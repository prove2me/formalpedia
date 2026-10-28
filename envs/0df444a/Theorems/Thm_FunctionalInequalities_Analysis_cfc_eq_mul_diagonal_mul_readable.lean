-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_cfc_eq_mul_diagonal_mul_readable
-- name    : FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:27.050427+00:00
-- url     : https://prove2.me/theorems/09ddc3bd-8df9-4276-88d0-412e386bc91f
-- title:
--   Real Spectral Functional Calculus Formula
-- statement:
--   This identifies the functional calculus of a finite real Hermitian matrix in an orthonormal eigenbasis.
--
--   Let $n$ be a finite index type, let $A\in M_n(\mathbb R)$ be Hermitian, and let $f:\mathbb R\to\mathbb R$. If $U$ is the orthonormal eigenvector unitary of $A$ and $\lambda_i$ are its eigenvalues, then
--
--   $$
--   \operatorname{cfc}(f,A)=U\,\operatorname{diag}(f(\lambda_i))\,U^{\mathsf T}.
--   $$
--
--   The Lean declaration is `cfc_eq_mul_diagonal_mul_readable`. It is an exact finite-dimensional identity and does not assert any inequality or regularity property of $f$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cfc_eq_mul_diagonal_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
--       cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => f (hA.eigenvalues i)) *
--         (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Trace/Power`](https://prove2.me/theorems/dacdf9e6-5e72-4350-bea3-13b172a49586).
--
--   [Source excerpt, lines 170–172](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Power.lean#L170-L172) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Power.lean#L169-L194 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Power`, declaration `FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Power

open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_readable {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by sorry
