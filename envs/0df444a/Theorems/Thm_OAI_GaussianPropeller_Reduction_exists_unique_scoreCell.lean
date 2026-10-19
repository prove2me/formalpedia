-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_unique_scoreCell
-- name    : OAI.GaussianPropeller.Reduction.exists_unique_scoreCell
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:53:44.36112+00:00
-- url     : https://prove2.me/theorems/6837006a-4b1d-425f-9d84-dbe60ed0d04d
-- title:
--   Every point lies in exactly one score cell
-- statement:
--   Let $v_1,\dots,v_k\in\mathbb R^d$ with $k\ge1$. The score cell of $i$ is the set of $x$ such that $\langle v_i,x\rangle$ is maximal among the $\langle v_j,x\rangle$, with $\langle v_j,x\rangle<\langle v_i,x\rangle$ for every $j<i$. For every $x$ there is exactly one $i$ with
--   $$
--   x\in\mathrm{Cell}_i(v).
--   $$
--
--   So the score cells form a partition of all of $\mathbb R^d$, with ties broken towards the smallest index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Dual.lean#L107-L135

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.exists_unique_scoreCell (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by sorry
