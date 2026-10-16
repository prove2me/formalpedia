-- Prove2me | Theorems.Thm_OAI_Problem310_ScaleDiscretization_exists_dyadic_grid_representatives
-- name    : OAI.Problem310.ScaleDiscretization.exists_dyadic_grid_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:35:57.903982+00:00
-- url     : https://prove2.me/theorems/2e4b5d50-ec2f-433e-b5ea-7409e75b60a1
-- title:
--   Common scale representatives for the dyadic grid cells of the points $x+t\,2^{-n_i}$
-- statement:
--   Let $\iota$ be a finite index set with $|\iota|$ elements, let $x\in\mathbb{R}$, and let $B_i,n_i\in\mathbb{N}$ for $i\in\iota$ and $L\in\mathbb{N}$ satisfy the padding condition $B_i\le n_i+L$ for every $i$.
--
--   **Theorem.** There is a finite set $R\subseteq[1,2]$ with $|R|\le 1+|\iota|\,2^L$ such that for every $t\in[1,2]$ there is $t'\in R$ with
--
--   $$\Bigl\lfloor 2^{B_i}\bigl(x+t'\,2^{-n_i}\bigr)\Bigr\rfloor=\Bigl\lfloor 2^{B_i}\bigl(x+t\,2^{-n_i}\bigr)\Bigr\rfloor\qquad\text{for all } i\in\iota .$$
--
--   In words, for each $i$ the point $x+t\,2^{-n_i}$ lies in the same cell of the dyadic grid of mesh $2^{-B_i}$ as $x+t'\,2^{-n_i}$. As the scale $t$ ranges over $[1,2]$, all these grid positions are captured by at most $1+|\iota|\,2^L$ representative scales. This is the deterministic discretization of the dilation parameter used when affine copies of dyadic points are tested against tables indexed by dyadic cells.
--
--   **Formalization Note** The statement writes $2^{-n_i}$ as $((2:\mathbb{R})^{-1})^{n_i}$, and $|\iota|$ is `Fintype.card ι`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/MonotoneRepresentatives.lean#L138-L160

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel

open OAI OAI.Problem310
universe u_α u_ι
open scoped BigOperators

theorem OAI.Problem310.ScaleDiscretization.exists_dyadic_grid_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by sorry
