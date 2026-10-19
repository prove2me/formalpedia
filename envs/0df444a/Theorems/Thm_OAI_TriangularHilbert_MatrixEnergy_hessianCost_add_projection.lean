-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_add_projection
-- name    : OAI.TriangularHilbert.MatrixEnergy.hessianCost_add_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:40:42.122534+00:00
-- url     : https://prove2.me/theorems/37fc32d9-90a9-4a27-8920-8fc20cbbe549
-- title:
--   Adding a kernel projection does not change the Hessian cost
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. The Hessian cost is $\mathrm{hessianCost}(P,K)=\frac32\sup_X\bigl(2\langle K,X\rangle-\langle X,\sqrt PX+X\sqrt P\rangle\bigr)$, which equals $\frac32\langle K,Y\rangle$ whenever $\sqrt PY+Y\sqrt P=K$. Let $P\ge0$, and let $Q$ be an orthogonal projection with $PQ=QP=0$ and $P+Q$ positive definite, so that $Q$ projects onto the kernel of $P$. If $KQ=QK=0$, then
--   $$
--   \mathrm{hessianCost}(P+Q,K)=\mathrm{hessianCost}(P,K).
--   $$
--
--   Directions supported away from the kernel do not see the regularizing projection.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Support.lean#L59-L93

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

theorem OAI.TriangularHilbert.MatrixEnergy.hessianCost_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianCost (P + Q) K = hessianCost P K := by sorry
