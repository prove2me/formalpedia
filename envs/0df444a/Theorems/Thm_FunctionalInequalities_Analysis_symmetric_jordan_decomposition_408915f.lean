-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_jordan_decomposition_408915f
-- name    : FunctionalInequalities.Analysis.symmetric_jordan_decomposition_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:08.505772+00:00
-- url     : https://prove2.me/theorems/9d435507-843e-4c14-b4a1-64db9fcaa5be
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
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L258-L320 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_jordan_decomposition`; the repository is private at upload time).

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
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section Jordan
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_jordan_decomposition_408915f (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    ∃ P N : Matrix ι ι ℝ,
      P.PosSemidef ∧ N.PosSemidef ∧ B = P - N ∧
      P * N = 0 ∧ N * P = 0 ∧
      (B * B).trace = (P * P).trace + (N * N).trace := by sorry
