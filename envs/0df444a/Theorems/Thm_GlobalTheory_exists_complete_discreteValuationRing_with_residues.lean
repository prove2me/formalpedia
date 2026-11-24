-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_with_residues
-- name    : GlobalTheory.exists_complete_discreteValuationRing_with_residues
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:14.672459+00:00
-- url     : https://prove2.me/theorems/1964fbfe-7bc7-4f59-94a5-eba20643c2ec
-- title:
--   Global Theory: exists complete discrete Valuation Ring with residues
-- statement:
--   The Global Theory construction uses the exists complete discrete Valuation Ring with residues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L157-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L157-L176

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

theorem GlobalTheory.exists_complete_discreteValuationRing_with_residues :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      (r : O →+* Ω) (S : Finset Ω), RingHom.ker r = IsLocalRing.maximalIdeal O →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (j : O →+* O') (r' : O' →+* Ω), IsAdicComplete (IsLocalRing.maximalIdeal O') O' ∧
        Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧
        RingHom.ker r' = IsLocalRing.maximalIdeal O' ∧ ∀ a ∈ S, a ∈ Set.range r' := by sorry
