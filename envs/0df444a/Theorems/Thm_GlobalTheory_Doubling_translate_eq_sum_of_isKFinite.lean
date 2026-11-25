-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_translate_eq_sum_of_isKFinite
-- name    : GlobalTheory.Doubling.translate_eq_sum_of_isKFinite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:41.803533+00:00
-- url     : https://prove2.me/theorems/b825e505-0e97-5127-a3ee-a950bdf96782
-- title:
--   Doubling: translate eq sum of is KFinite
-- statement:
--   The Doubling construction uses the translate eq sum of is KFinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslateEqSumOfIsKFinite.lean#L6-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslateEqSumOfIsKFinite.lean#L6-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslateEqSumOfIsKFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Doubling

theorem GlobalTheory.Doubling.translate_eq_sum_of_isKFinite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} {f : G → ℂ} (hf : Continuous f) (hK : IsKFinite K f) :
    ∃ (m : ℕ) (kk : Fin m → G) (c : Fin m → G → ℂ), (∀ j, kk j ∈ K) ∧ (∀ j, Continuous (c j)) ∧
      ∀ g, ∀ k ∈ K, f (g * k) = ∑ j, c j k * f (g * kk j) := by sorry
