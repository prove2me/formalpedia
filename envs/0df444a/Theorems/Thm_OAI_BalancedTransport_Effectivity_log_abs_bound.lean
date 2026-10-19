-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_log_abs_bound
-- name    : OAI.BalancedTransport.Effectivity.log_abs_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:20:42.627021+00:00
-- url     : https://prove2.me/theorems/a5b525db-0231-4222-9109-879804b13855
-- title:
--   An integer bound on the logarithm of a positive rational
-- statement:
--   For every rational $q>0$,
--   $$
--   |\log q|\le|\mathrm{num}(q)|+|\mathrm{num}(q^{-1})|,
--   $$
--   where $\mathrm{num}$ denotes the numerator in lowest terms.
--
--   This gives the computable magnitude bound for the logarithm operation of numeric programs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveLog.lean#L132-L146

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Filter
open scoped Topology

theorem OAI.BalancedTransport.Effectivity.log_abs_bound {q : ℚ} (hq : 0 < q) :
    |Real.log (q : ℝ)| ≤ (q.num.natAbs + q⁻¹.num.natAbs : ℕ) := by sorry
