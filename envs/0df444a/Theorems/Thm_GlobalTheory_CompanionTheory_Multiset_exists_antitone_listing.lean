-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Multiset_exists_antitone_listing
-- name    : GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:29.556601+00:00
-- url     : https://prove2.me/theorems/251f4906-6adc-470b-9006-1a4fa0759e62
-- title:
--   Multiset: exists antitone listing
-- statement:
--   The Multiset construction uses the exists antitone listing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetAntitoneEnumeration.lean#L5-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetAntitoneEnumeration.lean#L5-L31

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetAntitoneEnumeration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Multiset

theorem GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop)
    (hP : ∀ a b, P a b → f a < f b) :
    ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧
      ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by sorry
