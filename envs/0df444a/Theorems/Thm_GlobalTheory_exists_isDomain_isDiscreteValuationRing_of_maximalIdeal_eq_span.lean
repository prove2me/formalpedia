-- Prove2me | Theorems.Thm_GlobalTheory_exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span
-- name    : GlobalTheory.exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:17.679698+00:00
-- url     : https://prove2.me/theorems/404d0c90-c938-4897-886a-cebf5c284da3
-- title:
--   Global Theory: exists is Domain is Discrete Valuation Ring of maximal Ideal eq span
-- statement:
--   The Global Theory construction uses the exists is Domain is Discrete Valuation Ring of maximal Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvr.lean#L31-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvr.lean#L31-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {t : S} (ht : maximalIdeal S = Ideal.span {t})
    (hreg : IsSMulRegular S t) : ∃ _ : IsDomain S, IsDiscreteValuationRing S := by sorry
