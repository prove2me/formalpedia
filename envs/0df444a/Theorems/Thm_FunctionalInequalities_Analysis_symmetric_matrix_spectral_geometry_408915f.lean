-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_symmetric_matrix_spectral_geometry_408915f
-- name    : FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:11.417866+00:00
-- url     : https://prove2.me/theorems/c9c9cd01-f0e6-449f-aec9-7fb4ff9692e1
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean#L349-L404 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Sign`, declaration `FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry`; the repository is private at upload time).

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
open scoped MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 700000

theorem FunctionalInequalities.Analysis.symmetric_matrix_spectral_geometry_408915f {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hunit : IsUnit M) :
    let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (M*M)
    let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt B
    let Q : Matrix (Fin n) (Fin n) ℝ := cfc (fun x : ℝ => (SignType.sign x : ℝ)) M
    B.PosSemidef ∧ S.PosSemidef ∧ Q.IsSymm ∧ B*B=M*M ∧ S*S=B ∧ S*Q*S=M ∧ Q*Q=1 ∧ IsUnit S ∧
    IsSelfAdjoint (Matrix.toEuclideanLin Q).toContinuousLinearMap ∧
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      e.toContinuousLinearMap = (Matrix.toEuclideanLin S).toContinuousLinearMap ∧
      IsSelfAdjoint e.toContinuousLinearMap := by sorry
