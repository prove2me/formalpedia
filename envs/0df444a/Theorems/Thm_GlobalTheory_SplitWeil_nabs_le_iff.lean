-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_nabs_le_iff
-- name    : GlobalTheory.SplitWeil.nabs_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:38.908627+00:00
-- url     : https://prove2.me/theorems/0e66a13a-3c92-44a2-9513-8dfdc5d7d86f
-- title:
--   Split Weil: nabs le iff
-- statement:
--   The Split Weil construction uses the nabs le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L49-L51

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

theorem GlobalTheory.SplitWeil.nabs_le_iff (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) := by sorry
