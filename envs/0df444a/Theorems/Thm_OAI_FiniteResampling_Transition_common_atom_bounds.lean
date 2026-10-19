-- Prove2me | Theorems.Thm_OAI_FiniteResampling_Transition_common_atom_bounds
-- name    : OAI.FiniteResampling.Transition.common_atom_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:54:55.334949+00:00
-- url     : https://prove2.me/theorems/e028af4d-18aa-45a3-b821-a37d0348e4f1
-- title:
--   One step of a transition with a common atom
-- statement:
--   Let $K$ be a stochastic matrix on a finite nonempty set $I$ ($K(i,j)\ge0$, $\sum_jK(i,j)=1$), acting on functions by $(Kf)(i)=\sum_jK(i,j)f(j)$. If every row gives weight at least $a$ to a common state $z$, i.e. $K(i,z)\ge a$ for all $i$, then for every $f$ and $i$,
--   $$
--   af(z)+(1-a)\min f\le(Kf)(i)\le af(z)+(1-a)\max f .
--   $$
--
--   This is a Doeblin minorization step.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Resampling.lean#L65-L88

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

theorem OAI.FiniteResampling.Transition.common_atom_bounds (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by sorry
