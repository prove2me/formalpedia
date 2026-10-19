-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_sqrt_pooled
-- name    : OAI.DiamondDistortion.FiniteAverage.sqrt_pooled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:37:33.571626+00:00
-- url     : https://prove2.me/theorems/45a65fe3-c704-4832-b620-f27a3b44ac22
-- title:
--   Midpoint concavity bound $\sqrt{\eta}+\sqrt{\eta+2\theta}\le 2\sqrt{\eta+\theta}$
-- statement:
--   For all real numbers $\eta\ge0$ and $\theta\ge0$,
--   $$
--   \sqrt{\eta}+\sqrt{\eta+2\theta}\le2\sqrt{\eta+\theta}.
--   $$
--
--   This is midpoint concavity of the square root at the points $\eta$ and $\eta+2\theta$, whose midpoint is $\eta+\theta$: the average of $\sqrt\eta$ and $\sqrt{\eta+2\theta}$ is at most $\sqrt{\eta+\theta}$. It is used to pool two square-root budgets of the form $\sqrt{\eta}$ and $\sqrt{\eta+2\theta}$ into a single one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean#L163-L177

import Mathlib
import Definitions.Def_DiamondDistortion

open OAI OAI.DiamondDistortion
universe u v
open scoped BigOperators Classical Topology
open Set
variable {Ω : Type*} [Fintype Ω]

theorem OAI.DiamondDistortion.FiniteAverage.sqrt_pooled {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    Real.sqrt η + Real.sqrt (η+2*θ) ≤ 2*Real.sqrt (η+θ) := by sorry
