-- Prove2me | Theorems.Thm_GlobalTheory_algHom_sub_constantCoeff_mem
-- name    : GlobalTheory.algHom_sub_constantCoeff_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:35.852583+00:00
-- url     : https://prove2.me/theorems/a574e462-c7ec-476f-8de9-b1ea708460ab
-- title:
--   Global Theory: alg Hom sub constant Coeff mem
-- statement:
--   The Global Theory construction uses the alg Hom sub constant Coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L97-L103

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

theorem GlobalTheory.algHom_sub_constantCoeff_mem (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) (g : MvPowerSeries σ A) :
    φ g - algebraMap A S (constantCoeff g) ∈ K := by sorry
