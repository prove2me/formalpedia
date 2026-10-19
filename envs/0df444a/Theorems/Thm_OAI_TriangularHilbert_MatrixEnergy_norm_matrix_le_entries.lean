-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_norm_matrix_le_entries
-- name    : OAI.TriangularHilbert.MatrixEnergy.norm_matrix_le_entries
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:47:51.023568+00:00
-- url     : https://prove2.me/theorems/71f7c38e-a3e0-4d48-b6c9-c35cbdfff43c
-- title:
--   Operator norm bounded by the largest entry
-- statement:
--   Let $R$ be a complex square matrix indexed by a finite set $\iota$ with $|R_{ij}|\le M$ for all $i,j$. Then
--   $$
--   \|R\|\le C_\iota\,M,\qquad C_\iota=\sum_{i,j}\|E_{ij}\| ,
--   $$
--   where $E_{ij}$ are the matrix units and $\|\cdot\|$ is the $\ell^2$ operator norm.
--
--   Entrywise bounds give operator norm bounds with a constant depending only on the size of the matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/NormBounds.lean#L89-L103

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem OAI.TriangularHilbert.MatrixEnergy.norm_matrix_le_entries (R : Matrix ι ι ℂ) {M : ℝ} (hM : ∀ i j, ‖R i j‖ ≤ M) :
    ‖R‖ ≤ entryNormConstant ι * M := by sorry
