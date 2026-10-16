-- Prove2me | Theorems.Thm_OAI_Problem310_WindowLocalFactor_exists_uniform_window_representatives
-- name    : OAI.Problem310.WindowLocalFactor.exists_uniform_window_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:38:16.41878+00:00
-- url     : https://prove2.me/theorems/717aadd1-f59c-43ad-8784-07439030bdaf
-- title:
--   Uniform scale representatives for all tests factoring through padded dyadic windows
-- statement:
--   Let $\Omega$ be an arbitrary set (of outcomes), let $M,r\in\mathbb{N}$, and let $a_i,B_i\in\mathbb{N}$ for $i\in\{0,\dots,M-1\}$ satisfy the padding condition $B_i+1\le a_i+2r$ for every $i$. Fix $x\in\mathbb{R}$ and write $\{w\}=w-\lfloor w\rfloor$ for the fractional part. Say that a family of Boolean tests $Q(\omega,i,y)\in\{\mathrm{true},\mathrm{false}\}$, for $\omega\in\Omega$, $i<M$ and $y\in\mathbb{R}$, *factors through the grids* $B$ if for all $\omega,i,y,z$
--   $$\bigl\lfloor 2^{B_i+2}\{y\}\bigr\rfloor=\bigl\lfloor 2^{B_i+2}\{z\}\bigr\rfloor\ \Longrightarrow\ Q(\omega,i,y)=Q(\omega,i,z).$$
--
--   **Theorem.** There is a finite set $R\subseteq[1,2]$ with $|R|\le 1+M\,r\,2^{2r+2}$ such that for every $t\in[1,2]$ there is $t'\in R$ with the following property: for every family $Q$ that factors through the grids $B$, every $\omega\in\Omega$, every $i<M$ and every $j\in\{0,\dots,r-1\}$,
--
--   $$Q\bigl(\omega,i,\,x+t'\,2^{-(a_i+j)}\bigr)=Q\bigl(\omega,i,\,x+t\,2^{-(a_i+j)}\bigr).$$
--
--   One should think of child $i$ as carrying the window of dyadic scales $a_i,a_i+1,\dots,a_i+r-1$, all windows having the same length $r$. The essential point is the order of quantifiers: the representative scale $t'$ is chosen from $R$ before the outcome $\omega$ and before the tests $Q$, so a single deterministic finite set of scales serves all outcomes and all such tests at once.
--
--   **Formalization Note** The tests are functions `Q : Ω → Fin M → ℝ → Bool`, and $2^{-(a_i+j)}$ is written `((2 : ℝ)⁻¹) ^ (a i + j.val)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowLocalFactor.lean#L15-L44

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
universe u_Ω
open RoutingPath GridSeparation

theorem OAI.Problem310.WindowLocalFactor.exists_uniform_window_representatives {Ω : Type u_Ω} (M r : ℕ)
    (a B : Fin M → ℕ) (hpadding : ∀ i, B i + 1 ≤ a i + 2 * r)
    (x : ℝ) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + M * r * 2 ^ (2 * r + 2) ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : Ω → Fin M → ℝ → Bool,
          (∀ ω i y z, ⌊(2 : ℝ) ^ (B i + 2) * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ (B i + 2) * Int.fract z⌋ → Q ω i y = Q ω i z) →
          ∀ ω (i : Fin M) (j : Fin r),
            Q ω i (x + t' * ((2 : ℝ)⁻¹) ^ (a i + j.val)) =
              Q ω i (x + t * ((2 : ℝ)⁻¹) ^ (a i + j.val)) := by sorry
