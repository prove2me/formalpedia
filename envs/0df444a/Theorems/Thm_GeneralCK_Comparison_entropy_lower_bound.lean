-- Prove2me | Theorems.Thm_GeneralCK_Comparison_entropy_lower_bound
-- name    : GeneralCK.Comparison.entropy_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:21:22.117275+00:00
-- url     : https://prove2.me/theorems/2a859554-f489-430a-8cbf-89aa982c9916
-- title:
--   The explicit entropy trajectory bounds every admissible supersolution
-- statement:
--   Let $0<\varepsilon<1/2$ and $T\ge0$. Suppose $\delta$ is continuous on $[0,T]$, has right derivative $\delta^\prime$ on $[0,T)$, takes values in $(0,1]$ there, and satisfies $\eta(\delta(t))\le\delta^\prime(t)$ and $H(\varepsilon)\le\delta(0)$. For $q_\varepsilon(t)=(1-e^{-2t}(1-2\varepsilon))/2$, $$H(q_\varepsilon(T))\le\delta(T).$$ This comparison turns the entropy-production estimate into the required channel entropy bound.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyComparison.lean#L106-L132

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
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Comparison
end GeneralCK.Comparison
open GeneralCK GeneralCK.Comparison
open Set

theorem GeneralCK.Comparison.entropy_lower_bound {eps T : ℝ} {delta delta' : ℝ → ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T)
    (hc : ContinuousOn delta (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt delta (delta' t) (Ici t) t)
    (hrange : ∀ t ∈ Ico 0 T, delta t ∈ Ioc 0 1)
    (hprod : ∀ t ∈ Ico 0 T, eta (delta t) ≤ delta' t)
    (h0 : H eps ≤ delta 0) : H (noiseParameter eps T) ≤ delta T := by sorry
