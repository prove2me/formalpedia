-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution
-- name    : OAI.TriangularHilbert.MatrixEnergy.rootCost_eq_of_solution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:36:02.546053+00:00
-- url     : https://prove2.me/theorems/4043c9a4-5e76-40e3-8b4b-1d5a3fd97d11
-- title:
--   Root cost via a solution of the Sylvester equation
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. The root cost is $\mathrm{rootCost}(A,K)=\frac32\sup_X\bigl(2\langle K,X\rangle-\langle X,AX+XA\rangle\bigr)$. If $A$ is positive semidefinite and $Y$ solves $AY+YA=K$, then
--   $$
--   \mathrm{rootCost}(A,K)=\frac32\,\langle K,Y\rangle .
--   $$
--
--   The supremum of the quadratic variational problem is attained at the Sylvester solution.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L442-L455

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
variable {ι : Type uι} [Fintype ι]

theorem OAI.TriangularHilbert.MatrixEnergy.rootCost_eq_of_solution {A K Y : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hY : sylv A Y = K) : rootCost A K = (3 / 2 : ℝ) * hsReal K Y := by sorry
