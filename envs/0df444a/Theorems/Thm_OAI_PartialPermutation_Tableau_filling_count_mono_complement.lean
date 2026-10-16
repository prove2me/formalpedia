-- Prove2me | Theorems.Thm_OAI_PartialPermutation_Tableau_filling_count_mono_complement
-- name    : OAI.PartialPermutation.Tableau.filling_count_mono_complement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:37:56.295525+00:00
-- url     : https://prove2.me/theorems/4f1b18e9-39c6-494f-9181-323dff009a75
-- title:
--   Removing a lower set does not increase the number of linear extensions
-- statement:
--   Let $\alpha$ be a finite partially ordered set. A *standard filling* of $\alpha$ (a linear extension) is a bijection $e:\alpha\to\{0,1,\dots,|\alpha|-1\}$ that is strictly increasing: $a<b$ implies $e(a)<e(b)$. Write $\mathcal{E}(\alpha)$ for the number of standard fillings of $\alpha$. Let $P\subseteq\alpha$ be a *lower set*, i.e. $a\le b$ and $b\in P$ imply $a\in P$, and give the complement $\alpha\setminus P$ the order induced from $\alpha$. Then
--
--   $$
--   \mathcal{E}(\alpha\setminus P)\le\mathcal{E}(\alpha).
--   $$
--
--   For the cells of a Young diagram, ordered componentwise, standard fillings are exactly standard Young tableaux. The statement therefore says that deleting a down-closed set of cells, such as an initial segment of the first row, produces a skew shape with no more standard tableaux than the original diagram; it is used to transfer lower bounds from such skew shapes to the diagram itself.
--
--   **Formalization Note** $P$ is a decidable predicate with `IsLowerSet {a | P a}`, the complement is the subtype `{a // ¬P a}`, and `StandardFilling α` consists of equivalences `α ≃ Fin (Fintype.card α)` that are `StrictMono`; $\mathcal{E}$ is `Fintype.card (StandardFilling _)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/FillingExtensions.lean#L75-L88

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

open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset
variable {α β : Type*} [Fintype α] [PartialOrder α] [Fintype β] [PartialOrder β]

theorem OAI.PartialPermutation.Tableau.filling_count_mono_complement (P : α → Prop) [DecidablePred P]
    (hP : IsLowerSet {a | P a}) :
    Fintype.card (StandardFilling {a // ¬P a}) ≤ Fintype.card (StandardFilling α) := by sorry
