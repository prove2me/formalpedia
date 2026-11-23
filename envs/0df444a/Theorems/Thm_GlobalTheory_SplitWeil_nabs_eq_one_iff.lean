-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff
-- name    : GlobalTheory.SplitWeil.nabs_eq_one_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:39.271475+00:00
-- url     : https://prove2.me/theorems/98c4458b-7d48-4dab-a8b2-0b18e649318a
-- title:
--   Split Weil: nabs eq one iff
-- statement:
--   The Split Weil construction uses the nabs eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L56-L57

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

theorem GlobalTheory.SplitWeil.nabs_eq_one_iff (x : kˣ) : nabs k x = 1 ↔ valuation k (x : k) = 1 := by sorry
