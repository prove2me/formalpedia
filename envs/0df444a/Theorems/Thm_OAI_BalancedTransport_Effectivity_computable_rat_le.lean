-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_rat_le
-- name    : OAI.BalancedTransport.Effectivity.computable_rat_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:05:35.521513+00:00
-- url     : https://prove2.me/theorems/1c027803-3c49-4ea0-b031-464ca03bf31d
-- title:
--   Comparison of rationals is computable
-- statement:
--   The map
--   $$
--   (a,b)\mapsto\begin{cases}\text{true}&a\le b\\\text{false}&a>b\end{cases}
--   $$
--   on pairs of rational numbers is computable.
--
--   This lets algorithms branch on comparisons of rational approximations, for instance when choosing between the two pieces of a glued velocity field.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean#L28-L41

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity

theorem OAI.BalancedTransport.Effectivity.computable_rat_le : Computable₂ (fun a b : ℚ => decide (a ≤ b)) := by sorry
