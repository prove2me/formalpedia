-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hsCube_weightedArray_le
-- name    : OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:07:58.184845+00:00
-- url     : https://prove2.me/theorems/91a8c712-41e4-4e6f-a244-b924c1363cfc
-- title:
--   Hilbert–Schmidt cube of a weighted edge
-- statement:
--   Let $A$ be a triangle array and $g_v(i)\ge0$ weights with $\sum_ig_v(i)\le M$ for every vertex $v$. The weighted edge $v$ has entries $\sqrt{g_v(i)}A_v(i,j)\sqrt{g_{v+1}(j)}$. Its Hilbert–Schmidt norm satisfies
--   $$
--   \|\text{weighted edge }v\|_{\mathrm{HS}}^3\le M\sum_{i,j}|A_v(i,j)|^3\,g_v(i)\,g_{v+1}(j).
--   $$
--
--   The cubic Hilbert–Schmidt size of a weighted edge is controlled by its heat-weighted cubic mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/InitialAlgebra.lean#L74-L93

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
variable {ι : Type uι} [Fintype ι]

theorem OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ v, (∑ i, g v i) ≤ M) (v : Three) :
    hsCube (weightedArray A g v) ≤ M * ∑ i, ∑ j, ‖A v i j‖^3 * (g v i*g (v+1) j) := by sorry
