-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_continuous_heatMask
-- name    : OAI.TriangularHilbert.Heat.continuous_heatMask
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:51:16.331236+00:00
-- url     : https://prove2.me/theorems/598a27ee-3700-4ab9-9647-5578e4455312
-- title:
--   Continuity of diagonal heat masks
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. For real numbers $d_w(j)$, $\mathrm{heatMask}(d)$ is the block diagonal matrix with diagonal entries $d_w(j)$ at index $(w,j)$.
--
--   If each entry $x\mapsto r(x)_w(j)$ is continuous on a topological space, then
--   $$
--   x\longmapsto\mathrm{heatMask}\bigl(r(x)\bigr)
--   $$
--   is continuous. In particular masks of scores and second scores vary continuously with the centres and variances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatContinuous.lean#L54-L67

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι uE
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem OAI.TriangularHilbert.Heat.continuous_heatMask {E : Type uE} [TopologicalSpace E] {r : E → Three → ι → ℝ}
    (hr : ∀ w j, Continuous (fun x => r x w j)) : Continuous (fun x => heatMask (r x)) := by sorry
