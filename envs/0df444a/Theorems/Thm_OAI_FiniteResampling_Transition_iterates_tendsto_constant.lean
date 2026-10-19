-- Prove2me | Theorems.Thm_OAI_FiniteResampling_Transition_iterates_tendsto_constant
-- name    : OAI.FiniteResampling.Transition.iterates_tendsto_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:55:34.001585+00:00
-- url     : https://prove2.me/theorems/e30bd2a8-3ef6-49f2-92ae-ce1233b4f77f
-- title:
--   Iterates of a transition with a common atom converge to a constant
-- statement:
--   Let $K$ be a stochastic matrix on a finite nonempty set $I$ ($K(i,j)\ge0$, $\sum_jK(i,j)=1$), acting on functions by $(Kf)(i)=\sum_jK(i,j)f(j)$. If $0<a\le1$ and $K(i,z)\ge a$ for all $i$ and some fixed state $z$, then for every $f$ there is a constant $c$ with $\min f\le c\le\max f$ such that
--   $$
--   (K^nf)(i)\to c\quad\text{for every }i .
--   $$
--
--   The limit is the same for all starting states.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Resampling.lean#L97-L149

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling

open OAI OAI.FiniteResampling OAI.FiniteResampling.Transition
universe uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open scoped BigOperators Matrix
open Filter
variable {I : Type uI} [Fintype I] [Nonempty I]
variable (K : Transition I)

theorem OAI.FiniteResampling.Transition.iterates_tendsto_constant (z : I) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : ∀ i, a ≤ K.weight i z) (f : I → ℝ) :
    ∃ c : ℝ, lower f ≤ c ∧ c ≤ upper f ∧
      ∀ i, Tendsto (fun n : ℕ => ((K.act)^[n] f) i) atTop (nhds c) := by sorry
