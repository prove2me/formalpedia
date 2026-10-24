-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_symmetric_isUnit_matrix_sequence_408915f
-- name    : FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:52.806538+00:00
-- url     : https://prove2.me/theorems/13a3e7c5-4f52-4b36-a04d-de979ec90829
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
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L416-L435 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence`; the repository is private at upload time).

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

noncomputable section
open scoped MatrixOrder
noncomputable section
open Matrix Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 300000

theorem FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence_408915f {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ∃ seq : ℕ → Matrix ι ι ℝ,
      (∀ k, (seq k).IsSymm ∧ IsUnit (seq k)) ∧ Tendsto seq atTop (𝓝 A) := by sorry
