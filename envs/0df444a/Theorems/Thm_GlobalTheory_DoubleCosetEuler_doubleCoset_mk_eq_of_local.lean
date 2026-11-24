-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetEuler_doubleCoset_mk_eq_of_local
-- name    : GlobalTheory.DoubleCosetEuler.doubleCoset_mk_eq_of_local
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:11.193575+00:00
-- url     : https://prove2.me/theorems/72213826-997a-4ae5-9966-52426251eefe
-- title:
--   Double Coset Euler: double Coset mk eq of local
-- statement:
--   The Double Coset Euler construction uses the double Coset mk eq of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetEqFinprodLocalSums.lean#L64-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetEqFinprodLocalSums.lean#L64-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.DoubleCosetEuler

theorem GlobalTheory.DoubleCosetEuler.doubleCoset_mk_eq_of_local (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (S0 : Finset ι)
    (hsurj : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (g g' : G) (hg : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k)
    (hg' : ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g' = t * k)
    (h : ∀ i ∈ S0, DoubleCoset.mk (TH i) (KH i) (p i g) = DoubleCoset.mk (TH i) (KH i) (p i g')) :
    DoubleCoset.mk T K g = DoubleCoset.mk T K g' := by sorry
