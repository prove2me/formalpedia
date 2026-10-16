-- Prove2me | Theorems.Thm_OAI_PartialPermutation_Tableau_binomial_lower_bound
-- name    : OAI.PartialPermutation.Tableau.binomial_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:41:01.766106+00:00
-- url     : https://prove2.me/theorems/39a835db-229c-4514-a2ff-e768226eb71d
-- title:
--   A binomial lower bound for standard Young tableaux from the first row
-- statement:
--   Let $\mu$ be a Young diagram with $n$ cells whose first row has length $\lambda_1$, and let $f^\mu$ be the number of standard Young tableaux of shape $\mu$, i.e. of bijections from the cells of $\mu$ to $\{0,1,\dots,n-1\}$ that increase strictly along every row and down every column. For every natural number $b$ with $b\le\min(\lambda_1,\,n-\lambda_1)$,
--
--   $$
--   \binom{\lambda_1}{b}\le f^\mu .
--   $$
--
--   Here $n-\lambda_1$ is the number of cells below the first row. Applied to $\mu$ or to its transpose, the bound gives lower estimates for $f^\mu$, the degree of the irreducible representation of $S_n$ indexed by $\mu$, in terms of the longest line of $\mu$ and the number of cells outside it.
--
--   **Formalization Note** $\lambda_1$ is `μ.rowLen 0`, $n$ is `μ.cells.card`, the difference `μ.cells.card - μ.rowLen 0` is natural-number subtraction (no truncation occurs since $\lambda_1\le n$), and $f^\mu$ is `standardCount μ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Truncation.lean#L105-L118

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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation

open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset

theorem OAI.PartialPermutation.Tableau.binomial_lower_bound (μ : YoungDiagram) (b : ℕ)
    (hb : b ≤ min (μ.rowLen 0) (μ.cells.card-μ.rowLen 0)) :
    (μ.rowLen 0).choose b ≤ standardCount μ := by sorry
