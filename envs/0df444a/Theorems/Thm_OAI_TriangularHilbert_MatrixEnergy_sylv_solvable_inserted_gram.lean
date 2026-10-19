-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_sylv_solvable_inserted_gram
-- name    : OAI.TriangularHilbert.MatrixEnergy.sylv_solvable_inserted_gram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:38:00.110232+00:00
-- url     : https://prove2.me/theorems/2c2345c6-6b7b-4934-8ffb-a7aa74d77f74
-- title:
--   Sylvester equations for inserted Gram matrices are solvable
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. Let $R$ be a rectangular complex matrix and $D$ a square matrix on its row space. Then the Sylvester equation for the square root of the Gram matrix $R^*R$ with right-hand side $R^*DR$ is solvable:
--   $$
--   \exists\,Y:\quad\sqrt{R^*R}\,Y+Y\sqrt{R^*R}=R^*DR .
--   $$
--
--   Inserted Gram matrices never charge the kernel of the Gram matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L830-L863

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
variable [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.sylv_solvable_inserted_gram {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (D : Matrix κ κ ℂ) :
    ∃ Y, sylv (CFC.sqrt (Rᴴ * R)) Y = Rᴴ * D * R := by sorry
