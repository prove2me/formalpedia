-- Prove2me | Theorems.Thm_OAI_PartialPermutation_Tableau_fixed_deficit_growth
-- name    : OAI.PartialPermutation.Tableau.fixed_deficit_growth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:41:52.439594+00:00
-- url     : https://prove2.me/theorems/1d1f3c10-af52-4c88-9f45-72c9ff838cf9
-- title:
--   Standard Young tableaux grow at least linearly for a fixed positive deficit
-- statement:
--   Let $\mu$ be a Young diagram with $n$ cells, let $\lambda_1$ be the length of its first row and $\lambda_1'$ the length of its first column, and let $L(\mu)=\max(\lambda_1,\lambda_1')$ be the length of its longest line. The *deficit* of $\mu$ is $k=n-L(\mu)$, the number of cells outside a longest row or column. Let $f^\mu$ be the number of standard Young tableaux of shape $\mu$ (bijections from the cells to $\{0,\dots,n-1\}$ increasing along rows and down columns). If $k>0$ and $2k\le n$, then
--
--   $$
--   n-2k+1\le f^\mu .
--   $$
--
--   Diagrams of deficit $0$ consist of a single row or a single column and have $f^\mu=1$. For every fixed positive deficit the number of standard tableaux, which is the degree of the corresponding irreducible representation of $S_n$, grows at least linearly in $n$; such bounds control sums of negative powers of degrees over diagrams of small deficit.
--
--   **Formalization Note** $L(\mu)$ is `maxLine μ = max (μ.rowLen 0) (μ.colLen 0)` and $k$ is `deficit μ = μ.cells.card - maxLine μ` (natural-number subtraction, no truncation since $L(\mu)\le n$). The left-hand side `μ.cells.card - 2*deficit μ + 1` is natural-number arithmetic, and the hypothesis $2k\le n$ makes the subtraction exact.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TailBounds.lean#L112-L125

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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds

open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset

theorem OAI.PartialPermutation.Tableau.fixed_deficit_growth (μ : YoungDiagram) (hk : 0 < deficit μ)
    (hlarge : 2*deficit μ ≤ μ.cells.card) :
    μ.cells.card-2*deficit μ+1 ≤ standardCount μ := by sorry
