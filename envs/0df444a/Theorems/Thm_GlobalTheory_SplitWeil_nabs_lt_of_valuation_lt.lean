-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_nabs_lt_of_valuation_lt
-- name    : GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:13.864239+00:00
-- url     : https://prove2.me/theorems/fbc4eb88-17d6-4cef-b267-3ab6a576d0f9
-- title:
--   Split Weil: nabs lt of valuation lt
-- statement:
--   The Split Weil construction uses the nabs lt of valuation lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L27-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NormalizedAbsCharacterization.lean#L27-L47

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

theorem GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by sorry
