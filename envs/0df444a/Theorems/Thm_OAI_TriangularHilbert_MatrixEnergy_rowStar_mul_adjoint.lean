-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rowStar_mul_adjoint
-- name    : OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:43:54.024991+00:00
-- url     : https://prove2.me/theorems/629c80a1-fe3c-457e-8749-46004578118c
-- title:
--   A star row times its adjoint is block diagonal
-- statement:
--   A triangle array $W=(W_0,W_1,W_2)$ defines the $3\times3$ block matrix with $W_0,W_1,W_2$ in the cyclic positions $(0,1),(1,2),(2,0)$ and their adjoints in the transposed positions. $\mathrm{rowStar}(W,v)$ is its block row $v$ (other rows set to zero). For every vertex $v$,
--   $$
--   \mathrm{rowStar}(A,v)\,\mathrm{rowStar}(A,v)^*=\mathrm{blockD}\bigl(w\mapsto[w=v]\ \mathrm{centerGram}(A,v)\bigr),
--   $$
--   where $\mathrm{centerGram}(A,v)=\sum_wT_{vw}T_{vw}^*$ is the sum over the blocks $T_{vw}$ of row $v$ of the triangle matrix.
--
--   The outer Gram matrix of a star row lives on the single vertex $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/WeightedStar.lean#L114-L138

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v * (rowStar A v)ᴴ =
      blockD (fun w => if w = v then centerGram A v else 0) := by sorry
