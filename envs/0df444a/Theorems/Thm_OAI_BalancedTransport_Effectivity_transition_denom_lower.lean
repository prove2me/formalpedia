-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_transition_denom_lower
-- name    : OAI.BalancedTransport.Effectivity.transition_denom_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:05:10.349136+00:00
-- url     : https://prove2.me/theorems/8108f90e-107c-4612-bbb3-d36304ab1d79
-- title:
--   The denominator of the smooth transition is at least 1/9
-- statement:
--   Let $\rho(x)=e^{-1/x}$ for $x>0$ and $\rho(x)=0$ for $x\le0$. Then for every real $x$,
--   $$
--   \frac19\le\rho(x)+\rho(1-x).
--   $$
--
--   The smooth transition from $0$ to $1$ is $S(x)=\rho(x)/(\rho(x)+\rho(1-x))$. This lower bound on its denominator makes the derivatives of $S$ explicitly bounded and computable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FlatBounds.lean#L96-L113

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial

theorem OAI.BalancedTransport.Effectivity.transition_denom_lower (x : ℝ) :
    1 / 9 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by sorry
