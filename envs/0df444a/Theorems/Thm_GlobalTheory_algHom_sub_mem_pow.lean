-- Prove2me | Theorems.Thm_GlobalTheory_algHom_sub_mem_pow
-- name    : GlobalTheory.algHom_sub_mem_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:59.093411+00:00
-- url     : https://prove2.me/theorems/83844bed-063e-4a16-80c3-082b1704c89e
-- title:
--   Global Theory: alg Hom sub mem pow
-- statement:
--   The Global Theory construction uses the alg Hom sub mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L120-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L120-L135

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

theorem GlobalTheory.algHom_sub_mem_pow (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (hψ : ∀ i, ψ (X i) ∈ J) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ J ^ n) (g : MvPowerSeries σ A) : φ g - ψ g ∈ J ^ n := by sorry
