-- Prove2me | Theorems.Thm_OAI_PartialPermutation_Tableau_truncateLower_topRow
-- name    : OAI.PartialPermutation.Tableau.truncateLower_topRow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:39:38.460773+00:00
-- url     : https://prove2.me/theorems/37f4b8f1-1e7c-40c0-8808-e4daa409ea15
-- title:
--   Truncating the part of a Young diagram below the first row keeps the first row
-- statement:
--   Let $\mu$ be a Young diagram, viewed as a finite set of cells $(r,c)\in\mathbb{N}^2$ (row $r$, column $c$, both counted from $0$) that is closed downward in the componentwise order. For a Young diagram $\nu$ write $\lambda_1(\nu)$ for the length of its first row (row $0$). Let $\mu_{\mathrm{low}}=\{(r,c)\in\mu:r\neq0\}$ be the set of cells outside the first row with the componentwise order, and let $T$ be a standard filling of $\mu_{\mathrm{low}}$, i.e. a bijection $T:\mu_{\mathrm{low}}\to\{0,\dots,|\mu_{\mathrm{low}}|-1\}$ with $T(x)<T(y)$ whenever $x<y$. For $b\in\mathbb{N}$, the *truncation* of $\mu$ is
--
--   $$
--   \mu^{T,b}=\{(0,c)\in\mu\}\ \cup\ \{x\in\mu_{\mathrm{low}}:T(x)<b\},
--   $$
--
--   the whole first row of $\mu$ together with the cells below it whose $T$-label is smaller than $b$; it is again a Young diagram because $T$ is increasing. For every such $\mu$, $T$ and $b$,
--
--   $$
--   \lambda_1\bigl(\mu^{T,b}\bigr)=\lambda_1(\mu).
--   $$
--
--   When $b\le|\mu_{\mathrm{low}}|$, the truncation is a subdiagram of $\mu$ consisting of the full first row and exactly $b$ further cells. It is used to prove the lower bound $\binom{\lambda_1(\mu)}{b}\le f^\mu$ for the number $f^\mu$ of standard Young tableaux, and this lemma records that the first row is untouched.
--
--   **Formalization Note** $\mu^{T,b}$ is `truncateLower μ T b`, defined by filtering `μ.cells` with the condition that the cell lies in `μ` and, if its row index is nonzero, its label under `T` is less than `b`; $\lambda_1$ is `rowLen 0`. No hypothesis on `b` is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Truncation.lean#L45-L58

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

theorem OAI.PartialPermutation.Tableau.truncateLower_topRow (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) :
    (truncateLower μ T b).rowLen 0 = μ.rowLen 0 := by sorry
