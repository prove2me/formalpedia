-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_cfc_eq_mul_diagonal_mul_408915f
-- name    : FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:18.300801+00:00
-- url     : https://prove2.me/theorems/0d00e8f7-296e-4457-9f31-174c315eb0e4
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
--   The Lean declaration is `cfc_eq_mul_diagonal_mul`. It is an exact finite-dimensional identity and does not assert any inequality or regularity property of $f$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Trace/Power.lean#L169-L194 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Trace.Power`, declaration `FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul`; the repository is private at upload time).

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem FunctionalInequalities.Analysis.cfc_eq_mul_diagonal_mul_408915f {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by sorry
