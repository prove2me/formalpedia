-- Prove2me | Theorems.Thm_GlobalTheory_ResidueExtension_injective_of_map_ne_zero
-- name    : GlobalTheory.ResidueExtension.injective_of_map_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:20:58.995035+00:00
-- url     : https://prove2.me/theorems/fe2a5d68-42f6-46df-8f83-d471217d9683
-- title:
--   Residue Extension: injective of map ne zero
-- statement:
--   The Residue Extension construction uses the injective of map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L12-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]

theorem GlobalTheory.ResidueExtension.injective_of_map_ne_zero {B : Type} [CommRing B] [IsDomain B] (j : O →+* B) {π : O}
    (hπ : Irreducible π) (h : j π ≠ 0) : Function.Injective j := by sorry
