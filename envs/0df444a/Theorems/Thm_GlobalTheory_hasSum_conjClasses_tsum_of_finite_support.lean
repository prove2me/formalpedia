-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_conjClasses_tsum_of_finite_support
-- name    : GlobalTheory.hasSum_conjClasses_tsum_of_finite_support
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:47:26.242375+00:00
-- url     : https://prove2.me/theorems/70473160-8ccd-42bf-aa4a-747f4b67362b
-- title:
--   Global Theory: has Sum conj Classes tsum of finite support
-- statement:
--   The Global Theory construction uses the has Sum conj Classes tsum of finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumConjClassesRegroupWithInvariantSelection.lean#L5-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumConjClassesRegroupWithInvariantSelection.lean#L5-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumConjClassesRegroupWithInvariantSelection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.hasSum_conjClasses_tsum_of_finite_support {G : Type} [Group G] (g : G → ℂ) (hg : (Function.support g).Finite)
    (R : G → Prop) (hR : ∀ δ, g δ ≠ 0 → R δ) :
    HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ)
      (∑' δ, g δ) := by sorry
