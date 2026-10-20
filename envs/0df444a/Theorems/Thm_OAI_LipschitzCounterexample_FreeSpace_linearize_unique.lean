-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_linearize_unique
-- name    : OAI.LipschitzCounterexample.FreeSpace.linearize_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:24:37.111607+00:00
-- url     : https://prove2.me/theorems/bec39ad0-9b65-42af-af52-71268af668c9
-- title:
--   Uniqueness of the linearization of a Lipschitz map
-- statement:
--   Let $M$ be a pointed metric space, $F$ a real Banach space and $D:M\to F$ a $K$-Lipschitz map with $D(0)=0$. If a bounded operator $T:\mathcal F(M)\to F$ satisfies $T(\delta_x)=D(x)$ for all $x\in M$, then
--   $$
--   T=\hat D ,
--   $$
--   where $\hat D$ is the linearization of $D$.
--
--   So the linearization is the unique bounded linear extension of $D$ through $x\mapsto\delta_x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/FreeSpace.lean#L266-L282

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM uF
open scoped NNReal ENNReal
variable (M : Type uM) [MetricSpace M] [Zero M]
variable {M}
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (D : M → F) {K : ℝ≥0} (hD : LipschitzWith K D) (h0 : D 0 = 0)
include hD h0
variable [CompleteSpace F]

theorem OAI.LipschitzCounterexample.FreeSpace.linearize_unique (T : Space M →L[ℝ] F) (hT : ∀ x, T (point x) = D x) :
    linearize D = T := by sorry
