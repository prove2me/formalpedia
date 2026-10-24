-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sqrt_real_cfc_bridge_408915f
-- name    : FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:10.398763+00:00
-- url     : https://prove2.me/theorems/d5186a68-e24a-4702-80f5-3a2904ef0b77
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L40-L64 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge`; the repository is private at upload time).

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
section FiniteIndex
variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge_408915f
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    0 ≤ M * M ∧
      CFC.sqrt (M * M) = cfc (fun x : ℝ => Real.sqrt x) (M * M) ∧
      0 ≤ CFC.sqrt (M * M) ∧
      CFC.sqrt (CFC.sqrt (M * M)) =
        cfc (fun x : ℝ => Real.sqrt x) (CFC.sqrt (M * M)) := by sorry
