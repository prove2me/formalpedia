-- Prove2me | Theorems.Thm_GeneralCK_Comparison_antitone_ode_comparison
-- name    : GeneralCK.Comparison.antitone_ode_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:21:05.580533+00:00
-- url     : https://prove2.me/theorems/8c3e3528-9e97-45f1-90c8-28806ae4e586
-- title:
--   Comparison for an antitone scalar differential field
-- statement:
--   Let $T\ge0$ and let $F$ be antitone on a set $S\subseteq\mathbb R$. Let $u,v$ be continuous on $[0,T]$ and right-differentiable on $[0,T)$, with values in $S$ there. Suppose $u^\prime(t)\le F(u(t))$, $F(v(t))\le v^\prime(t)$, and $u(0)\le v(0)$. Then $$u(T)\le v(T).$$ No derivative of $F$ or inverse entropy function is assumed.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyComparison.lean#L35-L54

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

theorem GeneralCK.Comparison.antitone_ode_comparison {field u v u' v' : ℝ → ℝ} {s : Set ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hf : AntitoneOn field s)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hdu : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hus : ∀ t ∈ Ico 0 T, u t ∈ s) (hvs : ∀ t ∈ Ico 0 T, v t ∈ s)
    (hu' : ∀ t ∈ Ico 0 T, u' t ≤ field (u t))
    (hv' : ∀ t ∈ Ico 0 T, field (v t) ≤ v' t)
    (h0 : u 0 ≤ v 0) : u T ≤ v T := by sorry
