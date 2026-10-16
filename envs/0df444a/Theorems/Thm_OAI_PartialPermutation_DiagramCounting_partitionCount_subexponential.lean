-- Prove2me | Theorems.Thm_OAI_PartialPermutation_DiagramCounting_partitionCount_subexponential
-- name    : OAI.PartialPermutation.DiagramCounting.partitionCount_subexponential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:42:20.696528+00:00
-- url     : https://prove2.me/theorems/59735f44-7672-4b3e-a774-cd5b9907521f
-- title:
--   The number of partitions of $n$ grows subexponentially
-- statement:
--   For $n\in\mathbb{N}$ let $p(n)$ be the number of Young diagrams with exactly $n$ cells, i.e. the number of partitions of $n$. For every real $\delta>0$ there is $N\in\mathbb{N}$ such that
--
--   $$
--   p(n)\le e^{\delta n}\qquad\text{for all }n\ge N .
--   $$
--
--   Since $p(n)$ is also the number of irreducible representations of the symmetric group $S_n$ up to isomorphism, the bound says that a sum over the irreducible representations of $S_n$ has only $e^{o(n)}$ terms. This is what is needed when sums such as $\sum_\pi d_\pi^{-u}$ over the degrees $d_\pi$ are bounded using degree estimates that grow exponentially in $n$; the bound is crude but sufficient for that purpose.
--
--   **Formalization Note** $p(n)$ is `partitionCount n`, the cardinality of `Shape n`, the type of Young diagrams with `n` cells. "For all sufficiently large $n$" is the filter statement `∀ᶠ n : ℕ in atTop`, and the right-hand side is `Real.exp (δ * n)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/PartitionAsymptotics.lean#L11-L45

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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts

open OAI OAI.PartialPermutation OAI.PartialPermutation.DiagramCounting
open Finset

open Filter in
theorem OAI.PartialPermutation.DiagramCounting.partitionCount_subexponential (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (partitionCount n : ℝ) ≤ Real.exp (δ*n) := by sorry
