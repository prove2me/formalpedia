-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_computable_rational
-- name    : OAI.BalancedTransport.Effectivity.NumericOp.computable_rational
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:21:56.292824+00:00
-- url     : https://prove2.me/theorems/0de76f66-2b98-4d34-8cae-6b677242afeb
-- title:
--   The rational semantics of numeric operations is computable
-- statement:
--   A numeric operation is one step of a straight-line program: a literal, a coordinate, a sum, a product, a negation, a guarded inverse, a derivative of $e^{-1/x}$, an exponential, or a logarithm of a rational literal. It reads earlier registers from a list. At a rational point $x\in\mathbb Q^d$, with $d\ge1$, and precision $p$, each operation produces a rational value from a list of rational registers. The map
--   $$
--   (o,x,p,s)\mapsto\text{the rational value of operation }o
--   $$
--   is computable.
--
--   Hence running a numeric program rationally is an algorithm, which yields effective approximations of elementary fields.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean#L121-L156

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

theorem OAI.BalancedTransport.Effectivity.NumericOp.computable_rational (d : ℕ) [NeZero d] :
    Computable (fun z : NumericOp × (Fin d → ℚ) × ℕ × List ℚ =>
      rational d z.1 z.2.1 z.2.2.1 z.2.2.2) := by sorry
