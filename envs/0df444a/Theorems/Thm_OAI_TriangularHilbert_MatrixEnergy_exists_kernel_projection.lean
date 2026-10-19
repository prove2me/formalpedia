-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_exists_kernel_projection
-- name    : OAI.TriangularHilbert.MatrixEnergy.exists_kernel_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:41:22.347749+00:00
-- url     : https://prove2.me/theorems/290dc876-47d4-4989-9a9e-631551649ff8
-- title:
--   Every positive semidefinite matrix has a complementary kernel projection
-- statement:
--   For every positive semidefinite complex matrix $P$ there is an orthogonal projection $Q$ ($Q\ge0$, $Q^2=Q$) with
--   $$
--   PQ=QP=0\qquad\text{and}\qquad P+Q\ \text{positive definite}.
--   $$
--
--   Namely $Q$ is the projection onto $\ker P$. Adding it regularizes $P$ without interacting with its range, which allows derivative formulas proved for positive definite matrices to be applied to singular Gram matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Support.lean#L95-L145

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.exists_kernel_projection {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧
      (P + Q).PosDef := by sorry
