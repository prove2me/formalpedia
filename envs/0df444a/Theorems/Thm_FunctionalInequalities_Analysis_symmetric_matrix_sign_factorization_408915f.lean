-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_sign_factorization_408915f
-- name    : FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:11.381638+00:00
-- url     : https://prove2.me/theorems/17b5d65b-97fa-45be-b92a-70fed5b8a4ea
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L105-L232 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization_408915f
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    let AbsM : Matrix ι ι ℝ := CFC.sqrt (M * M)
    let S : Matrix ι ι ℝ := CFC.sqrt AbsM
    let SignM : Matrix ι ι ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    S * S = AbsM ∧ S * SignM * S = M ∧
      (IsUnit M → SignM * SignM = 1) := by sorry
