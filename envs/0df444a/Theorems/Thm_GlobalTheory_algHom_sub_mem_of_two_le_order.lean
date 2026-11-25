-- Prove2me | Theorems.Thm_GlobalTheory_algHom_sub_mem_of_two_le_order
-- name    : GlobalTheory.algHom_sub_mem_of_two_le_order
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:56.052523+00:00
-- url     : https://prove2.me/theorems/6c575471-f1c5-4f0a-9e55-007463d6b6fc
-- title:
--   Global Theory: alg Hom sub mem of two le order
-- statement:
--   The Global Theory construction uses the alg Hom sub mem of two le order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L147-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L147-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]

theorem GlobalTheory.algHom_sub_mem_of_two_le_order (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J B : Ideal S}
    (hB : B ≤ J) (hφ : ∀ i, φ (X i) ∈ B) (hψ : ∀ i, ψ (X i) ∈ B) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ B * J ^ n) {g : MvPowerSeries σ A} (hg : 2 ≤ g.order) :
    φ g - ψ g ∈ B ^ 2 * J ^ n := by sorry
