-- Prove2me | Theorems.Thm_GlobalTheory_card_ker_int_matrix_four
-- name    : GlobalTheory.card_ker_int_matrix_four
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:49.641002+00:00
-- url     : https://prove2.me/theorems/8daab6d3-d8e5-48e7-a8ba-07805c732872
-- title:
--   Global Theory: card ker int matrix four
-- statement:
--   The Global Theory construction uses the card ker int matrix four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CardHomVanishingOfDiagBasis.lean#L23-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CardHomVanishingOfDiagBasis.lean#L23-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.card_ker_int_matrix_four (G : Type) [CommGroup G] (m r : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (hm : 1 ≤ m)
    (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hG : ∀ k : ℕ, k ∣ m → Nat.card {x : G // x ^ k = 1} = k ^ r) :
    Nat.card {ξ : Fin 4 → G // ∀ c, ∏ r', ξ r' ^ al r' c = 1} = m ^ (2 * r) := by sorry
