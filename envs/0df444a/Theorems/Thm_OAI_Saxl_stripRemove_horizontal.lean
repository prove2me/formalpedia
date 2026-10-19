-- Prove2me | Theorems.Thm_OAI_Saxl_stripRemove_horizontal
-- name    : OAI.Saxl.stripRemove_horizontal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:39:09.000024+00:00
-- url     : https://prove2.me/theorems/37103202-8f45-44b7-a093-b2d269d4ad24
-- title:
--   Deleting the bottom cells of the first $t$ columns of a Young diagram removes a horizontal strip
-- statement:
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. Equivalently, $\mu$ is given by weakly decreasing row lengths $\mu_0\ge\mu_1\ge\cdots$, and $(i,j)\in\mu$ if and only if $j<\mu_i$. A pair $\eta\subseteq\mu$ is a horizontal strip if no two cells of $\mu\setminus\eta$ lie in the same column.
--
--   For $t\in\mathbb{N}$ let $\mu^{\downarrow t}$ be the Young diagram with row lengths $\mu^{\downarrow t}_i=\max(\mu_i-t,0)+\min(t,\mu_{i+1})$ for $i\in\mathbb{N}$; these satisfy $\mu_{i+1}\le\mu^{\downarrow t}_i\le\mu_i$ and decrease weakly in $i$. Equivalently, $\mu^{\downarrow t}$ arises from $\mu$ by deleting the lowest cell of each nonempty column among the first $t$ columns. The theorem states that for every Young diagram $\mu$ and every $t\in\mathbb{N}$, $\mu^{\downarrow t}\subseteq\mu$ is a horizontal strip:
--
--   $$
--   \mu^{\downarrow t}\subseteq\mu\qquad\text{and}\qquad (i,j),(i',j)\in\mu\setminus\mu^{\downarrow t}\ \Longrightarrow\ i=i'.
--   $$
--
--   Since $|\mu|-|\mu^{\downarrow t}|=\min(t,\mu_0)$ (a separate counting lemma), this produces, for any requested size up to the first row length, a horizontal strip that can be peeled off $\mu$. It is the basic move in the construction of chains of horizontal strips behind the sufficiency part of Young's rule.
--
--   **Formalization Note** The diagram $\mu^{\downarrow t}$ is `stripRemove μ t`, the set of cells $(i,j)\in\mu$ with $j$ less than `stripRow μ t i`, which is $\mu_i-t+\min(t,\mu_{i+1})$ with truncated natural-number subtraction, i.e. $\max(\mu_i-t,0)+\min(t,\mu_{i+1})$. `HorizontalStrip η μ` is the conjunction of $\eta\le\mu$ and the column condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HorizontalRemoval.lean#L75-L91

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

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.stripRemove_horizontal (μ : YoungDiagram) (t : ℕ) : HorizontalStrip (stripRemove μ t) μ := by sorry
