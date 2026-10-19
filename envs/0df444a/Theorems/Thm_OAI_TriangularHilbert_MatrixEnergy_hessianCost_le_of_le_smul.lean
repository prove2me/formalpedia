-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_le_of_le_smul
-- name    : OAI.TriangularHilbert.MatrixEnergy.hessianCost_le_of_le_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:39:09.393319+00:00
-- url     : https://prove2.me/theorems/f78844d2-d0f8-4d4a-b75f-42e4081d1ead
-- title:
--   Monotonicity of the Hessian cost in the base matrix
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. The Hessian cost is $\mathrm{hessianCost}(P,K)=\frac32\sup_X\bigl(2\langle K,X\rangle-\langle X,\sqrt PX+X\sqrt P\rangle\bigr)$, which equals $\frac32\langle K,Y\rangle$ whenever $\sqrt PY+Y\sqrt P=K$. Let $Q\ge0$, $c>0$ and $P\le cQ$, and suppose the Sylvester equation $\sqrt PY+Y\sqrt P=K$ is solvable. Then
--   $$
--   \mathrm{hessianCost}(Q,K)\le\sqrt c\ \mathrm{hessianCost}(P,K).
--   $$
--
--   Enlarging the base matrix lowers the Hessian cost, with a loss of $\sqrt c$ for a rescaled comparison.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L1620-L1639

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι uκ uX uμ
open scoped BigOperators
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.hessianCost_le_of_le_smul {P Q K : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K)
    {c : ℝ} (hc : 0 < c) (hPQ : P ≤ c • Q) :
    hessianCost Q K ≤ Real.sqrt c * hessianCost P K := by sorry
