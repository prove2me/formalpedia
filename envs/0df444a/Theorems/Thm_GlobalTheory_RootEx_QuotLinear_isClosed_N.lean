-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_QuotLinear_isClosed_N
-- name    : GlobalTheory.RootEx.QuotLinear.isClosed_N
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:34.16717+00:00
-- url     : https://prove2.me/theorems/5df18c6c-0465-4809-a639-f736392e5af2
-- title:
--   Quot Linear: is Closed N
-- statement:
--   The Quot Linear construction uses the is Closed N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralLinear.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralLinear.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotLinear
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootEx.QuotLinear.isClosed_N : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by sorry
