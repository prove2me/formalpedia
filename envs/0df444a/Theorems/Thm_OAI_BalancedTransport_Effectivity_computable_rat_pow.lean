-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_rat_pow
-- name    : OAI.BalancedTransport.Effectivity.computable_rat_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:06:08.102988+00:00
-- url     : https://prove2.me/theorems/eb331984-0d55-43bd-b84d-8f23a62e492d
-- title:
--   Powers of rationals are computable
-- statement:
--   The map
--   $$
--   (q,n)\mapsto q^n,\qquad q\in\mathbb Q,\ n\in\mathbb N,
--   $$
--   is computable.
--
--   Powers of rational numbers occur in the Taylor approximations of the exponential and in the base-$B$ codes of words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean#L100-L111

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity

theorem OAI.BalancedTransport.Effectivity.computable_rat_pow : Computable₂ ((· ^ ·) : ℚ → ℕ → ℚ) := by sorry
