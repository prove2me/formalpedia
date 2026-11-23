-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
-- name    : GlobalTheory.SplitWeil.one_lt_resCard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:17.431817+00:00
-- url     : https://prove2.me/theorems/4b609629-e8ca-46c2-a954-534de5858723
-- title:
--   Split Weil: one lt res Card
-- statement:
--   The Split Weil construction uses the one lt res Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L13-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (k)

theorem GlobalTheory.SplitWeil.one_lt_resCard : 1 < resCard k := by sorry
