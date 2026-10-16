-- Prove2me | Theorems.Thm_OAI_PartialPermutation_Tableau_row_interleaving_lower_bound
-- name    : OAI.PartialPermutation.Tableau.row_interleaving_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:39:12.224442+00:00
-- url     : https://prove2.me/theorems/85a0238d-0e2d-41e0-9dc0-8f39cccc0261
-- title:
--   A binomial lower bound for standard Young tableaux from the first two rows
-- statement:
--   Let $\mu$ be a Young diagram with $n$ cells, and let $\lambda_1\ge\lambda_2$ be the lengths of its first and second rows, with $\lambda_2=0$ if $\mu$ has at most one row. Order the cells componentwise (a cell precedes another if it is weakly above and weakly to the left), and let $f^\mu$ be the number of standard Young tableaux of shape $\mu$, that is, of bijections from the cells of $\mu$ to $\{0,1,\dots,n-1\}$ that increase strictly along every row and down every column. Then
--
--   $$
--   \binom{n-\lambda_2}{n-\lambda_1}\le f^\mu .
--   $$
--
--   Here $n-\lambda_1$ is the number of cells below the first row. Since $f^\mu$ is the degree of the irreducible representation of the symmetric group $S_n$ indexed by $\mu$, this is a lower bound for that degree in terms of $n$ and the first two rows; it is the basic estimate from which the binomial bounds in terms of the first row and of the deficit are derived.
--
--   **Formalization Note** Rows are indexed from $0$ in Lean: $\lambda_1$ is `μ.rowLen 0`, $\lambda_2$ is `μ.rowLen 1`, and $n$ is `μ.cells.card`. The subtractions are natural-number subtractions; they do not truncate because $\lambda_2\le\lambda_1\le n$. $f^\mu$ is `standardCount μ`, the number of `StandardFilling`s of the cell poset `μ.cells`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/RowBounds.lean#L65-L89

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds

open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset

theorem OAI.PartialPermutation.Tableau.row_interleaving_lower_bound (μ : YoungDiagram) :
    (μ.cells.card-μ.rowLen 1).choose (μ.cells.card-μ.rowLen 0) ≤ standardCount μ := by sorry
