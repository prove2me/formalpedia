-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs
-- name    : GlobalTheory.SplitWeil.isLocallyConstant_nabs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:35.204658+00:00
-- url     : https://prove2.me/theorems/939b92c1-2a6c-4e9a-a7de-9c96c80ec6d7
-- title:
--   Split Weil: is Locally Constant nabs
-- statement:
--   The Split Weil construction uses the is Locally Constant nabs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L60-L71

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

theorem GlobalTheory.SplitWeil.isLocallyConstant_nabs : IsLocallyConstant (nabs k) := by sorry
