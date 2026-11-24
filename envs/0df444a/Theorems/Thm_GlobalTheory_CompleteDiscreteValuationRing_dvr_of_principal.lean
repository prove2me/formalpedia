-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_dvr_of_principal
-- name    : GlobalTheory.CompleteDiscreteValuationRing.dvr_of_principal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:10.72134+00:00
-- url     : https://prove2.me/theorems/3f228a09-4dfc-44ac-a81f-8577c79fd9c9
-- title:
--   Complete Discrete Valuation Ring: dvr of principal
-- statement:
--   The Complete Discrete Valuation Ring construction uses the dvr of principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L151-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDvrOfDimOne.lean#L151-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing

theorem GlobalTheory.CompleteDiscreteValuationRing.dvr_of_principal (S : Type) [CommRing S] [IsLocalRing S] (p : S)
    (hp : maximalIdeal S = Ideal.span {p}) (hreg : p ∈ nonZeroDivisors S)
    [IsHausdorff (maximalIdeal S) S] :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S := by sorry
