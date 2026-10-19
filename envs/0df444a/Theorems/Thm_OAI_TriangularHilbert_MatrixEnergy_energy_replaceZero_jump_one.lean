-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_replaceZero_jump_one
-- name    : OAI.TriangularHilbert.MatrixEnergy.energy_replaceZero_jump_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:02:43.608072+00:00
-- url     : https://prove2.me/theorems/cf25c6f7-7f37-41f9-b017-218aa7f93a57
-- title:
--   Energy jump of the vertex-one star when edge zero is changed
-- statement:
--   For a triangle array $W$ with weights $g_v(i)\ge0$, the weighted array has edges $\sqrt{g_v(i)}W_v(i,j)\sqrt{g_{v+1}(j)}$, and the star energy at vertex $v$ is $E(\mathrm{starGram}(\cdot,v))=\operatorname{tr}\bigl(R_v^*R_v\bigr)^{3/2}$ for the star row $R_v$. $\mathrm{replaceZero}(A,B)$ replaces the edge $0$ of $A$ by $B$. Let $B,C$ be entrywise dominated by $A_0$ and let $g\ge0$. Then the star energies at vertex $1$ of the weighted arrays $\mathrm{replaceZero}(A,B)$ and $\mathrm{replaceZero}(A,C)$ differ by at most
--   $$
--   \frac32\sum_{i,j}|B_{ij}-C_{ij}|\,g_0(i)g_1(j)\Bigl(\sum_m|A_0(m,j)|^2g_0(m)+\sum_m|A_1(j,m)|^2g_2(m)+\sum_m|A_0(i,m)|^2g_1(m)\Bigr).
--   $$
--
--   Edge $0$ also enters the star at vertex $1$, through its adjoint.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/StarJump.lean#L59-L88

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.energy_replaceZero_jump_one (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |energy (starGram (weightedArray (replaceZero A B) g) 1)-energy (starGram (weightedArray (replaceZero A C) g) 1)| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*
        ((∑ m, ‖A 0 m j‖^2*g 0 m)+(∑ m, ‖A 1 j m‖^2*g 2 m)+(∑ m, ‖A 0 i m‖^2*g 1 m)) := by sorry
