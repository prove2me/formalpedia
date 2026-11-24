-- Prove2me | Theorems.Thm_GlobalTheory_SBUniform_eventually_deep_subset
-- name    : GlobalTheory.SBUniform.eventually_deep_subset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:39.570048+00:00
-- url     : https://prove2.me/theorems/8d9aace8-f513-47ab-8769-40dc8a891cdd
-- title:
--   SBUniform: eventually deep subset
-- statement:
--   The SBUniform construction uses the eventually deep subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyDeepSubset.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyDeepSubset.lean#L25-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open Filter Topology
open GlobalTheory GlobalTheory.SBUniform
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SBUniform.eventually_deep_subset {s : Set k} (hs : s ∈ 𝓝 (0 : k)) :
    ∀ᶠ M : ℕ in atTop, ∀ x : k, Deep (M : ℤ) x → x ∈ s := by sorry
