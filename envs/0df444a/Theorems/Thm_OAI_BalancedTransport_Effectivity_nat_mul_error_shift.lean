-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_nat_mul_error_shift
-- name    : OAI.BalancedTransport.Effectivity.nat_mul_error_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:17:47.292852+00:00
-- url     : https://prove2.me/theorems/7a0d9ff7-3335-4535-8715-ab7a8972ca2f
-- title:
--   Absorbing a factor $k$ by $k$ extra bits of precision
-- statement:
--   For all natural numbers $n$ and $k$,
--   $$
--   k\cdot2^{-(n+k)}\le2^{-n}.
--   $$
--
--   Algorithms use this to absorb a known integer error multiplier $k$: requesting precision $n+k$ instead of $n$ makes $k$ accumulated errors fit into a total error of $2^{-n}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RelativeForce.lean#L84-L97

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity

theorem OAI.BalancedTransport.Effectivity.nat_mul_error_shift (n k : ℕ) : (k : ℝ) * error (n + k) ≤ error n := by sorry
