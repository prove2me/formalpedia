-- Prove2me | Theorems.Thm_GlobalTheory_CycFr_dvd_algHom_sub
-- name    : GlobalTheory.CycFr.dvd_algHom_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:38.142979+00:00
-- url     : https://prove2.me/theorems/6437bd2b-66c5-4e37-9b61-f0ea3a048a9d
-- title:
--   Cyc Fr: dvd alg Hom sub
-- statement:
--   The Cyc Fr construction uses the dvd alg Hom sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L336-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OneAddXMulDerivativeBin.lean#L336-L367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O]

theorem GlobalTheory.CycFr.dvd_algHom_sub [IsNoetherianRing O] (f g : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (hg : (X : O⟦X⟧) ∣ g X) (h : O⟦X⟧) (hh : h ∣ f X - g X) (a : O⟦X⟧) : h ∣ f a - g a := by sorry
