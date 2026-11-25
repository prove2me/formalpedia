-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetIndicator_exists_eq_sum_indicator
-- name    : GlobalTheory.DoubleCosetIndicator.exists_eq_sum_indicator
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:32.732645+00:00
-- url     : https://prove2.me/theorems/734dce17-be57-4b94-a2f9-1eea92cf3fe2
-- title:
--   Double Coset Indicator: exists eq sum indicator
-- statement:
--   The Double Coset Indicator construction uses the exists eq sum indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqSumIndicator.lean#L23-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqSumIndicator.lean#L23-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetIndicator

theorem GlobalTheory.DoubleCosetIndicator.exists_eq_sum_indicator {G : Type} [Group G] {M : Type} [AddCommMonoid M]
    (R K : Subgroup G) (T : Finset G) (φ : G → M)
    (hR : ∀ r ∈ R, ∀ x : G, φ (r * x) = φ x) (hK : ∀ κ ∈ K, ∀ x : G, φ (x * κ) = φ x)
    (hT : ∀ x : G, φ x ≠ 0 → ∃ t ∈ T, x ∈ dc R K t) :
    ∃ c : G → M, (∀ t : G, c t = 0 ∨ c t = φ t) ∧
      ∀ x : G, φ x = ∑ t ∈ T, Set.indicator (dc R K t) (fun _ => c t) x := by sorry
