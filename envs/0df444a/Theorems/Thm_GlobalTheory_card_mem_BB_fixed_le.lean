-- Prove2me | Theorems.Thm_GlobalTheory_card_mem_BB_fixed_le
-- name    : GlobalTheory.card_mem_BB_fixed_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:26.483238+00:00
-- url     : https://prove2.me/theorems/600996d8-f679-4676-8bc3-013daa22b62f
-- title:
--   Global Theory: card mem BB fixed le
-- statement:
--   The Global Theory construction uses the card mem BB fixed le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/DivLeRpowThreeQuarters.lean#L142-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/DivLeRpowThreeQuarters.lean#L142-L187

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.card_mem_BB_fixed_le (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ N : ℕ)
    (T : Finset ℕ) (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ ℓ ∈ Formalism.CyclotomicNorms.BB N g) :
    (T.card : ℝ) ≤ 1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by sorry
