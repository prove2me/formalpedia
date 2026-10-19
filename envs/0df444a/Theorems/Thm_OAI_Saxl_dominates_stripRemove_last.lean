-- Prove2me | Theorems.Thm_OAI_Saxl_dominates_stripRemove_last
-- name    : OAI.Saxl.dominates_stripRemove_last
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:39:59.532776+00:00
-- url     : https://prove2.me/theorems/0da7cff7-c584-4a5d-893d-747499d48ca6
-- title:
--   Dominance survives deleting the last row and a horizontal strip of the same length
-- statement:
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. Row lengths are weakly decreasing, $\mu_0\ge\mu_1\ge\cdots$, with $\mu_i=0$ for $i\ge\ell(\mu)$. For a Young diagram $\lambda$ and $q\in\mathbb{N}$ write $P_q(\lambda)=\sum_{i<q}\lambda_i$ for the number of cells in the first $q$ rows. A diagram $\tau$ dominates $\theta$, written $\tau\trianglerighteq\theta$, if $P_q(\theta)\le P_q(\tau)$ for every $q\in\mathbb{N}$.
--
--   For a diagram $\theta$ and $k\in\mathbb{N}$ let $\theta_{<k}$ be the diagram formed by the first $k$ rows of $\theta$ (the cells $(i,j)\in\theta$ with $i<k$). For $t\in\mathbb{N}$ let $\mu^{\downarrow t}$ be the Young diagram with row lengths $\mu^{\downarrow t}_i=\max(\mu_i-t,0)+\min(t,\mu_{i+1})$; equivalently, $\mu^{\downarrow t}$ arises from $\mu$ by deleting the lowest cell of each nonempty column among the first $t$ columns.
--
--   Let $\theta$ and $\tau$ be Young diagrams and $k\in\mathbb{N}$, and assume that $\theta$ has at most $k+1$ rows, that $|\tau|=|\theta|$, and that $\tau\trianglerighteq\theta$. Then, removing from $\tau$ a strip of length $\theta_k$,
--
--   $$
--   \bigl|\tau^{\downarrow\theta_k}\bigr|=\bigl|\theta_{<k}\bigr|\qquad\text{and}\qquad\tau^{\downarrow\theta_k}\ \trianglerighteq\ \theta_{<k}.
--   $$
--
--   Because $\theta$ has at most $k+1$ rows, $\theta_{<k}$ is $\theta$ with its last row (of length $\theta_k$, possibly $0$) deleted, while $\tau^{\downarrow\theta_k}\subseteq\tau$ is a horizontal strip with $\theta_k$ cells. Iterating this step builds a chain of horizontal strips of sizes $\theta_0,\theta_1,\dots$ from the empty diagram up to $\tau$, which is the combinatorial core of the sufficiency half of Young's rule.
--
--   **Formalization Note** `Dominates τ θ` is the prefix condition `∀ k, rowPrefix θ k ≤ rowPrefix τ k` only, so equality of sizes is a separate hypothesis. The diagrams are `rowTruncate θ k` and `stripRemove τ (θ.rowLen k)`, $\theta_k$ is `θ.rowLen k` (rows indexed from $0$), and "at most $k+1$ rows" is `θ.colLen 0 ≤ k+1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HorizontalRemoval.lean#L176-L208

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

theorem OAI.Saxl.dominates_stripRemove_last (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k+1) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    (stripRemove τ (θ.rowLen k)).card = (rowTruncate θ k).card ∧
      Dominates (stripRemove τ (θ.rowLen k)) (rowTruncate θ k) := by sorry
