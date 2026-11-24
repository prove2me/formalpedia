-- Prove2me | Theorems.Thm_GlobalTheory_lineDerivList_sum
-- name    : GlobalTheory.lineDerivList_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:54.833894+00:00
-- url     : https://prove2.me/theorems/9b24fdf4-8efa-4541-a9ba-622953e05ab0
-- title:
--   Global Theory: line Deriv List sum
-- statement:
--   The Global Theory construction uses the line Deriv List sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L167-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean#L167-L177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]

theorem GlobalTheory.lineDerivList_sum {κ : Type*} (s : Finset κ) {F : κ → E → V} {a : E}
    (hF : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a) (l : List E) :
    lineDerivList 𝕜 l (fun z => ∑ k ∈ s, F k z) a = ∑ k ∈ s, lineDerivList 𝕜 l (F k) a := by sorry
