-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Coding_interval_eq_image
-- name    : OAI.BalancedTransport.Coding.interval_eq_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:07:17.118985+00:00
-- url     : https://prove2.me/theorems/f7b4e9b2-b58e-4345-9c32-6a9f1c228f3f
-- title:
--   The coding interval of a word is the image of the unit interval
-- statement:
--   Fix $r>0$ and a digit map $\delta$ from an alphabet $S$ to $\mathbb R$. A word $w=a_1\cdots a_m$ has value $\mathrm{word}(w)=\sum_{i=1}^mr^i\delta(a_i)$, its prefixed points are $P_w(z)=\mathrm{word}(w)+r^mz$, and its coding interval is $I(w)=[\mathrm{word}(w),\mathrm{word}(w)+r^m]$. If $r>0$, then
--   $$
--   I(w)=P_w\bigl([0,1]\bigr).
--   $$
--
--   So the points of $I(w)$ are exactly the numbers obtained by writing $w$ in front of a number in $[0,1]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/PrefixCoding.lean#L192-L207

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding

open OAI OAI.BalancedTransport OAI.BalancedTransport.Coding
variable {S : Type*}

theorem OAI.BalancedTransport.Coding.interval_eq_image {r : ℝ} (hr : 0 < r) (digit : S → ℝ) (w : List S) :
    interval r digit w = prefixPoint r digit w '' Set.Icc (0 : ℝ) 1 := by sorry
