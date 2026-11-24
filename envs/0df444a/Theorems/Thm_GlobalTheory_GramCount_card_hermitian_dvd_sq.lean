-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_card_hermitian_dvd_sq
-- name    : GlobalTheory.GramCount.card_hermitian_dvd_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:39.561323+00:00
-- url     : https://prove2.me/theorems/3729e4e8-7f7e-4110-99ff-5be85f96546f
-- title:
--   Gram Count: card hermitian dvd sq
-- statement:
--   The Gram Count construction uses the card hermitian dvd sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianMatricesDvdSq.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianMatricesDvdSq.lean#L9-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.card_hermitian_dvd_sq {A : Type} [CommRing A] [Finite A] (c : A →+* A)
    (hc : ∀ u, c (c u) = u) (ω : A) (hω : IsUnit (ω - c ω)) (p : A) (hp : c p = p) (m : ℕ) :
    Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2
      = Nat.card {u : A // p ∣ u} ^ (m * m) := by sorry
