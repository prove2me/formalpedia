-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_weightedGram_rowBare_congr
-- name    : OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:44:29.41334+00:00
-- url     : https://prove2.me/theorems/13ee78c9-7176-4c8c-8a13-6e84d1cc1c20
-- title:
--   Weighted Gram matrices of a bare row see only one vertex
-- statement:
--   A triangle array $W=(W_0,W_1,W_2)$ defines the $3\times3$ block matrix with $W_0,W_1,W_2$ in the cyclic positions $(0,1),(1,2),(2,0)$ and their adjoints in the transposed positions. $\mathrm{rowStar}(W,v)$ is its block row $v$ (other rows set to zero). The bare row $\mathrm{rowBare}(A,g,v)=\mathrm{rowStar}(A,v)\,\mathrm{vertexRoot}(g)$ has nonzero rows only in block $v$. If two weight functions $f,f'$ on block indices agree on block $v$, i.e. $f(v,i)=f'(v,i)$ for all $i$, then
--   $$
--   \mathrm{weightedGram}(\mathrm{rowBare}(A,g,v),f)=\mathrm{weightedGram}(\mathrm{rowBare}(A,g,v),f').
--   $$
--
--   Weights on the other two vertices are invisible.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/WeightedCompare.lean#L31-L47

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

theorem OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (v : Three) (f f' : BlockSpace ι → ℝ) (he : ∀ i, f (v,i)=f' (v,i)) :
    weightedGram (rowBare A g v) f = weightedGram (rowBare A g v) f' := by sorry
