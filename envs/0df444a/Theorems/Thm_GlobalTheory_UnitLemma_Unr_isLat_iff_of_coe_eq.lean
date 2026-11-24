-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_isLat_iff_of_coe_eq
-- name    : GlobalTheory.UnitLemma.Unr.isLat_iff_of_coe_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:10.079248+00:00
-- url     : https://prove2.me/theorems/58ded3a1-1f71-425a-9340-cf58338a4746
-- title:
--   Unr: is Lat iff of coe eq
-- statement:
--   The Unr construction uses the is Lat iff of coe eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeOverUnramifiedExtIff.lean#L12-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeOverUnramifiedExtIff.lean#L12-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.isLat_iff_of_coe_eq {O O' E E' A : Type} [CommRing O] [CommRing O'] [Field E] [Field E'] [CommRing A]
    [Algebra O A] [Algebra O' A] [Algebra E A] [Algebra E' A] {d : ℕ} (u : Fin d → O')
    (h1 : ∀ a : O, ∃ b : O', algebraMap O' A b = algebraMap O A a)
    (h2 : ∀ y : O', ∃ a : Fin d → O, algebraMap O' A y = ∑ i, algebraMap O A (a i) * algebraMap O' A (u i))
    (h3 : ∀ e : E, ∃ e' : E', algebraMap E' A e' = algebraMap E A e)
    (h4 : ∀ e' : E', ∃ (e : E) (b : O'), algebraMap E' A e' = algebraMap E A e * algebraMap O' A b)
    (L : Submodule O' A) (M : Submodule O A) (h : (L : Set A) = (M : Set A)) :
    IsLat O' E' L ↔ IsLat O E M := by sorry
