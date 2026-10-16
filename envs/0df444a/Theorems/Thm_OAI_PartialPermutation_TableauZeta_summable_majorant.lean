-- Prove2me | Theorems.Thm_OAI_PartialPermutation_TableauZeta_summable_majorant
-- name    : OAI.PartialPermutation.TableauZeta.summable_majorant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:42:47.870555+00:00
-- url     : https://prove2.me/theorems/aabb954a-e493-476a-a5a0-651601415995
-- title:
--   Summability of the partition-weighted majorant $2\,p(k)\,2^{u}\,2^{-uk/8}$
-- statement:
--   For a natural number $k$, let $p(k)$ be the number of Young diagrams with exactly $k$ cells, that is, the number of integer partitions of $k$ (in particular $p(0)=1$, counting the empty diagram). For a real parameter $u$ consider the sequence
--
--   $$
--   M_u(k)=2\,p(k)\,\exp\!\Big(u\log 2-\frac{u\log 2}{8}\,k\Big)=2^{1+u}\,p(k)\,2^{-uk/8},\qquad k=0,1,2,\dots
--   $$
--
--   **Theorem.** If $u>0$, then the series of the nonnegative numbers $M_u(k)$ converges:
--
--   $$
--   \sum_{k=0}^{\infty}2\,p(k)\,\exp\!\Big(u\log 2-\frac{u\log 2}{8}\,k\Big)<\infty .
--   $$
--
--   Equivalently, the partition generating function $\sum_{k\ge 0}p(k)x^k$ converges at the point $x=2^{-u/8}$ of the open interval $(0,1)$.
--
--   The sequence $M_u$ serves as a summable majorant. Group the Young diagrams $\lambda$ with $n$ cells according to their deficit $k$, the number of cells outside a longest row or column, and let $f^\lambda$ be the number of standard Young tableaux of shape $\lambda$. For every $k\ge 1$ the total weight $\sum(f^\lambda)^{-u}$ carried by the diagrams of deficit $k$ is at most $M_u(k)$, uniformly in $n$. Summability of $M_u$ is therefore exactly what is needed to interchange the limit $n\to\infty$ with the sum over $k$ (dominated convergence for series, also known as Tannery's theorem) when showing that $\sum_{|\lambda|=n}(f^\lambda)^{-u}$ stays bounded as $n$ grows.
--
--   **Formalization Note** Here $p(k)$ is `partitionCount k`, the cardinality of the type `Shape k` of Mathlib `YoungDiagram`s with $k$ cells, and $M_u$ is `majorant u`, written with `Real.exp` and `Real.log`. For a real sequence, Lean's `Summable` means unconditional summability; for the nonnegative sequence $M_u$ this is the same as convergence of the series.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TableauWeights.lean#L35-L50

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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights

open OAI OAI.PartialPermutation OAI.PartialPermutation.TableauZeta
open Finset Filter
open Tableau DiagramCounting

theorem OAI.PartialPermutation.TableauZeta.summable_majorant (u : ℝ) (hu : 0 < u) : Summable (majorant u) := by sorry
