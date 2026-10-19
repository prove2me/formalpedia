-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hessianCost_inserted_gram_le
-- name    : OAI.TriangularHilbert.MatrixEnergy.hessianCost_inserted_gram_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:38:33.807356+00:00
-- url     : https://prove2.me/theorems/6ec8aa4e-f140-47ec-9015-b9df05fef6f1
-- title:
--   Hessian cost of an inserted Gram matrix
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. The Hessian cost is $\mathrm{hessianCost}(P,K)=\frac32\sup_X\bigl(2\langle K,X\rangle-\langle X,\sqrt PX+X\sqrt P\rangle\bigr)$, which equals $\frac32\langle K,Y\rangle$ whenever $\sqrt PY+Y\sqrt P=K$. Let $R$ be a square matrix and $L$ Hermitian. Then
--   $$
--   \mathrm{hessianCost}\bigl(R^*R,\ R^*LR\bigr)\le\frac34\,\|L\|^2\,E(R^*R).
--   $$
--
--   Inserting a bounded Hermitian matrix into a Gram matrix costs at most a multiple of the energy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L1509-L1536

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

theorem OAI.TriangularHilbert.MatrixEnergy.hessianCost_inserted_gram_le (R L : Matrix ι ι ℂ) (hL : L.IsHermitian) :
    hessianCost (Rᴴ * R) (Rᴴ * L * R) ≤
      (3 / 4 : ℝ) * ‖L‖^2 * energy (Rᴴ * R) := by sorry
