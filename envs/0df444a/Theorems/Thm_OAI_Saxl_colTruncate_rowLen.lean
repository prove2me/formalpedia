-- Prove2me | Theorems.Thm_OAI_Saxl_colTruncate_rowLen
-- name    : OAI.Saxl.colTruncate_rowLen
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:50:22.492031+00:00
-- url     : https://prove2.me/theorems/601e838d-a3c7-4e03-aa25-e6d15c6168d5
-- title:
--   Row lengths of the first $k$ columns of a Young diagram
-- statement:
--   Let $\mu$ be a Young diagram, viewed as a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) that is closed under moving up or to the left, and write $\mu_i$ for the length of row $i$, with $\mu_i=0$ when row $i$ is empty. For $k\in\mathbb{N}$ let $\mu^{[k]}$ be the column truncation of $\mu$, the Young diagram formed by the cells of $\mu$ in the first $k$ columns:
--   $$\mu^{[k]}=\{(i,j)\in\mu: j<k\}.$$
--   Then for every $k\in\mathbb{N}$ and every row index $i\in\mathbb{N}$,
--
--   $$\mu^{[k]}_i=\min(k,\mu_i).$$
--
--   Summing over $i$, the number of cells of $\mu$ in its first $k$ columns is $\sum_i\min(k,\mu_i)$, which is also the sum of the first $k$ column lengths of $\mu$, i.e. the $k$-th partial row sum of the conjugate diagram. This converts partial sums of the conjugate partition into data about the rows of $\mu$, and is the basic input for proving that conjugation reverses the dominance order.
--
--   **Formalization Note** The truncation is `colTruncate μ k`, defined as `(rowTruncate μ.transpose k).transpose`, where `rowTruncate ν k` keeps the cells of `ν` in rows $<k$; row lengths are Mathlib's `YoungDiagram.rowLen`. The identity holds for all $i$, including rows beyond the last row of $\mu$, where both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean#L19-L32

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport

open OAI OAI.Saxl
open scoped TensorProduct
universe uX uY

theorem OAI.Saxl.colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by sorry
