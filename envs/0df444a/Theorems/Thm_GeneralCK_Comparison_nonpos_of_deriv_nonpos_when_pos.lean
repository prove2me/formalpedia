-- Prove2me | Theorems.Thm_GeneralCK_Comparison_nonpos_of_deriv_nonpos_when_pos
-- name    : GeneralCK.Comparison.nonpos_of_deriv_nonpos_when_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:21:17.55441+00:00
-- url     : https://prove2.me/theorems/e352f2cd-9d14-41f0-bf96-2d24bd21f36a
-- title:
--   A scalar curve stays nonpositive under a right-derivative barrier
-- statement:
--   Let $T\ge0$. Suppose $g$ is continuous on $[0,T]$, has a right derivative $g^\prime(t)$ for $0\le t<T$, and $g(0)\le0$. If $g(t)>0$ implies $g^\prime(t)\le0$ throughout that half-open interval, then $$g(T)\le0.$$ This barrier lemma supports comparison of entropy trajectories.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyComparison.lean#L8-L33

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace GeneralCK.Comparison
end GeneralCK.Comparison
open GeneralCK GeneralCK.Comparison
open Set

theorem GeneralCK.Comparison.nonpos_of_deriv_nonpos_when_pos {g g' : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn g (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (h0 : g 0 ≤ 0)
    (hbound : ∀ t ∈ Ico 0 T, 0 < g t → g' t ≤ 0) : g T ≤ 0 := by sorry
