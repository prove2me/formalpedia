-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_vertexRoot_insert
-- name    : OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:46:28.86268+00:00
-- url     : https://prove2.me/theorems/c8c7e06f-7766-42d7-a0aa-40998b579ad3
-- title:
--   Inserting a diagonal between vertex roots
-- statement:
--   Let $g_v(i)\ge0$ and $d_v(i)$ be real weights indexed by a vertex $v\in\{0,1,2\}$ and a grid index $i$. Let $\mathrm{vertexRoot}(g)$ be the diagonal matrix with entries $\sqrt{g_v(i)}$ and $\mathrm{blockD}(d)$ the block diagonal matrix with diagonal blocks $\operatorname{diag}(d_v)$. Then
--   $$
--   \mathrm{vertexRoot}(g)\,\mathrm{blockD}(d)\,\mathrm{vertexRoot}(g)=\operatorname{diag}\bigl(g_v(i)\,d_v(i)\bigr)_{(v,i)} .
--   $$
--
--   Square roots of weights recombine into the weights themselves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/StarInsertion.lean#L83-L96

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert (g d : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) * vertexRoot g =
      Matrix.diagonal (fun a => (g a.1 a.2 * d a.1 a.2 : ℂ)) := by sorry
