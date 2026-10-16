-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_floor_multiple
-- name    : OAI.ShortEgyptian.floor_multiple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:53:47.157443+00:00
-- url     : https://prove2.me/theorems/2652c259-f4d6-4caf-a5e9-36e92808dfeb
-- title:
--   A positive multiple of $P$ in the interval $[X/2,X]$
-- statement:
--   Let $X$ be a real number and $P$ a positive integer with $P\le X$, and let $g=\lfloor X/P\rfloor\in\mathbb{N}$ be the integer part of $X/P$. Then
--
--   $$
--   g\ge 1\qquad\text{and}\qquad \frac X2\le gP\le X .
--   $$
--
--   Thus whenever $P\le X$, the interval $[X/2,X]$ contains a positive multiple of $P$, namely $\lfloor X/P\rfloor\,P$. In the construction of short Egyptian fraction expansions this lets one rescale a remainder fraction $A/C$ so that a numerator of the form $gP$ (with $P$ a multiple of $A$) lands in a window $[X/2,X]$, where it can be split as a sum of two numerators that are known to have short expansions.
--
--   **Formalization Note** The integer part is the natural-number floor `Nat.floor`, and the product $gP$ is computed in $\mathbb{N}$ and then cast to the reals. The hypotheses $P>0$ and $P\le X$ make $X/P\ge1$, so no truncation conventions matter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DenseSplit.lean#L50-L63

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.floor_multiple (X : ℝ) (P : ℕ) (hP : 0<P) (hPX : (P:ℝ)≤X) :
    let g := ⌊X/(P:ℝ)⌋₊
    0<g ∧ X/2 ≤ ((g*P:ℕ):ℝ) ∧ ((g*P:ℕ):ℝ)≤X := by sorry
