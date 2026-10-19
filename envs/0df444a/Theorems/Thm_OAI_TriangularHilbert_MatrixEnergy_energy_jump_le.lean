-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_jump_le
-- name    : OAI.TriangularHilbert.MatrixEnergy.energy_jump_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:01:17.014198+00:00
-- url     : https://prove2.me/theorems/6fffeeb6-6d19-4809-9ae0-73f0c494ae64
-- title:
--   Lipschitz bound for the matrix energy of Gram matrices
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$. For a matrix $M$ write $\|M_{i\cdot}\|$ and $\|M_{\cdot j}\|$ for the Euclidean norms of its rows and columns. If $A$ and $B$ are entrywise dominated by $M$, $|A_{ij}|,|B_{ij}|\le|M_{ij}|$, then
--   $$
--   \bigl|E(B^*B)-E(A^*A)\bigr|\le3\sum_{i,j}\|M_{i\cdot}\|\,\|M_{\cdot j}\|\,|(B-A)_{ij}| .
--   $$
--
--   Changing a few entries changes the energy by an amount weighted by the rows and columns they sit in.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/RankJump.lean#L68-L88

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.energy_jump_le (A B M : Matrix ι ι ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ ‖M i j‖) (hB : ∀ i j, ‖B i j‖ ≤ ‖M i j‖) :
    |energy (Bᴴ*B) - energy (Aᴴ*A)| ≤
      3 * ∑ i, ∑ j, rowNorm M i * colNorm M j * ‖(B-A) i j‖ := by sorry
