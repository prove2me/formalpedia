-- Prove2me | Theorems.Thm_GlobalTheory_SBUniform_exists_deep_subset
-- name    : GlobalTheory.SBUniform.exists_deep_subset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:32.933816+00:00
-- url     : https://prove2.me/theorems/a6073572-605c-4bac-9b76-b32f0fbafa64
-- title:
--   SBUniform: exists deep subset
-- statement:
--   The SBUniform construction uses the exists deep subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyDeepSubset.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyDeepSubset.lean#L39-L58

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

theorem GlobalTheory.SBUniform.exists_deep_subset {n : Type} [Fintype n] {s : Set (Matrix n n k)} (hs : s ∈ 𝓝 (0 : Matrix n n k)) :
    ∃ M : ℕ, ∀ y : Matrix n n k, (∀ i j, Deep (M : ℤ) (y i j)) → y ∈ s := by sorry
