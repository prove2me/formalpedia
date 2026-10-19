-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_computable_bound
-- name    : OAI.BalancedTransport.Effectivity.NumericOp.computable_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:22:37.044258+00:00
-- url     : https://prove2.me/theorems/ef4edd80-d182-4557-a52f-6d1dd4d9edad
-- title:
--   Bound propagation for numeric operations is computable
-- statement:
--   A numeric operation is one step of a straight-line program: a literal, a coordinate, a sum, a product, a negation, a guarded inverse, a derivative of $e^{-1/x}$, an exponential, or a logarithm of a rational literal. It reads earlier registers from a list. Each operation propagates a pair $(B,E)$ of natural numbers (a magnitude bound and an error multiplier) from the pairs of its operands and a coordinate bound $C$. The map
--   $$
--   (o,C,s)\mapsto\text{the bound pair of operation }o
--   $$
--   is computable.
--
--   So the precision needed to evaluate a program to error $2^{-n}$ is computable from the program.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean#L158-L201

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp

theorem OAI.BalancedTransport.Effectivity.NumericOp.computable_bound : Computable (fun z : NumericOp × ℕ × List (ℕ × ℕ) =>
    bound z.1 z.2.1 z.2.2) := by sorry
