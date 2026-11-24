-- Prove2me | Theorems.Thm_GlobalTheory_ResidueExtension_exists_step
-- name    : GlobalTheory.ResidueExtension.exists_step
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:38.756398+00:00
-- url     : https://prove2.me/theorems/5ee9e728-239a-4ffb-b25d-20fb7c43f6fc
-- title:
--   Residue Extension: exists step
-- statement:
--   The Residue Extension construction uses the exists step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L89-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L89-L121

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

theorem GlobalTheory.ResidueExtension.exists_step (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (a : Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ a ∈ Set.range r' := by sorry
