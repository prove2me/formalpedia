-- Prove2me | Theorems.Thm_GlobalTheory_T_multiset_antitone_enumeration
-- name    : GlobalTheory.T.multiset_antitone_enumeration
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:43.029918+00:00
-- url     : https://prove2.me/theorems/9b9dd5d8-ea63-45eb-945b-2a1be3a02906
-- title:
--   T: multiset antitone enumeration
-- statement:
--   The T construction uses the multiset antitone enumeration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetAntitoneEnumerationStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultisetAntitoneEnumerationStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetAntitoneEnumeration
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetAntitoneEnumerationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.multiset_antitone_enumeration : ∀ {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop), (∀ a b, P a b → f a < f b) → ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧ ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by sorry
