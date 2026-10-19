-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_starInsert_eq_insertRow
-- name    : OAI.TriangularHilbert.MatrixEnergy.starInsert_eq_insertRow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:39:41.097753+00:00
-- url     : https://prove2.me/theorems/d44b72cd-ad8e-4881-b3ae-7727b2529752
-- title:
--   Inserted star matrices as inserted Gram rows
-- statement:
--   A triangle array $W=(W_0,W_1,W_2)$ defines the $3\times3$ block matrix with $W_0,W_1,W_2$ in the cyclic positions $(0,1),(1,2),(2,0)$ and their adjoints in the transposed positions. $\mathrm{rowStar}(W,v)$ is its block row $v$ (other rows set to zero). For a block diagonal matrix $\mathrm{blockD}(D)$ with blocks $D_0,D_1,D_2$, the inserted star at vertex $v$ is $\mathrm{rowStar}(W,v)^*\,\mathrm{blockD}(D)\,\mathrm{rowStar}(W,v)$. It equals the inserted Gram row of the blocks $R_w$ of row $v$:
--   $$
--   \mathrm{starInsert}(W,D,v)=\bigl(R_w^*\,D_v\,R_{w'}\bigr)_{w,w'},\qquad R_w=\text{block }(v,w)\text{ of the triangle}.
--   $$
--
--   Only the block $D_v$ of the inserted diagonal matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean#L1741-L1756

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

theorem OAI.TriangularHilbert.MatrixEnergy.starInsert_eq_insertRow (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = insertRow (triangleBlocks W v) (D v) := by sorry
