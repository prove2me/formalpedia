-- Prove2me | Theorems.Thm_OAI_Saxl_strip_reduction
-- name    : OAI.Saxl.strip_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:51:58.487262+00:00
-- url     : https://prove2.me/theorems/797baae1-f984-4e1c-959c-2faec337c483
-- title:
--   Partitions not dominated by the staircase reduce to smaller staircase sizes by removing horizontal strips
-- statement:
--   A Young diagram is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$) closed under moving up or to the left; $\mu_i$ denotes the length of row $i$ (zero for empty rows) and $|\mu|$ the number of cells. For $\lambda,\mu$ say $\lambda$ dominates $\mu$ if $\sum_{i<k}\mu_i\le\sum_{i<k}\lambda_i$ for all $k\in\mathbb{N}$. For Young diagrams $\nu\subseteq\mu$, the skew shape $\mu/\nu$ is a horizontal strip if no two cells of $\mu\setminus\nu$ lie in the same column ($\nu=\mu$ is allowed). A strip chain of length $q$ from $\nu$ to $\mu$ is a sequence of Young diagrams $\nu=\eta_0\subsetneq\eta_1\subsetneq\cdots\subsetneq\eta_q=\mu$ in which every $\eta_j/\eta_{j-1}$ is a nonempty horizontal strip. The staircase $\delta_m=\{(i,j): i+j<m\}$ has rows of lengths $m,m-1,\dots,1$ and $|\delta_m|=m(m+1)/2$.
--
--   **Theorem.** Let $m\ge2$ and let $\mu$ be a Young diagram with $|\mu|=|\delta_m|$ that is not dominated by $\delta_m$. Then at least one of the following holds:
--
--   1. there is a Young diagram $\nu\subseteq\mu$ with $|\nu|=|\delta_{m-1}|=(m-1)m/2$ such that $\mu/\nu$ is a horizontal strip;
--   2. $m\ge5$, and there are $q\le4$ and a Young diagram $\nu$ with $|\nu|=|\delta_{m-2}|=(m-2)(m-1)/2$ together with a strip chain of length $q$ from $\nu$ to $\mu$.
--
--   In formulas:
--
--   $$\big(\exists\,\nu\subseteq\mu:\ |\nu|=|\delta_{m-1}|,\ \mu/\nu\text{ a horizontal strip}\big)\ \ \text{or}\ \ \big(m\ge5\ \text{and}\ \exists\,q\le4,\ \exists\,\nu:\ |\nu|=|\delta_{m-2}|,\ \nu=\eta_0\subsetneq\cdots\subsetneq\eta_q=\mu\big).$$
--
--   The removed cells number $m$ in the first case and $2m-1$ in the second. In an induction on the size of the staircase, this lets a shape that is not dominated by $\delta_m$ be reduced to a shape of the size of $\delta_{m-1}$, by one horizontal strip, or of $\delta_{m-2}$, by at most four horizontal strips. The removed strips are afterwards restored by a Pieri-type argument.
--
--   **Formalization Note** Horizontal strips are `HorizontalStrip ν μ` (`ν ≤ μ` and any two cells of `μ` outside `ν` in the same column are equal), strip chains are the inductive predicate `StripChain q ν μ` (each step a horizontal strip with `η ≠ μ`), and non-dominance is `¬ Dominates (staircase m) μ`. Sizes are written as `(staircase (m-1)).card` and `(staircase (m-2)).card`; truncated subtraction is harmless since $m\ge2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StripReduction.lean#L139-L161

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
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripReduction

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.strip_reduction (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ) :
    (∃ ν, ν.card = (staircase (m-1)).card ∧ HorizontalStrip ν μ) ∨
    (5 ≤ m ∧ ∃ q ≤ 4, ∃ ν, ν.card = (staircase (m-2)).card ∧ StripChain q ν μ) := by sorry
