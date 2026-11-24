-- Prove2me | Theorems.Thm_GlobalTheory_ResidueExtension_exists_completion
-- name    : GlobalTheory.ResidueExtension.exists_completion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:58.753799+00:00
-- url     : https://prove2.me/theorems/0e5cebf0-8a38-4634-af45-292676a7fd94
-- title:
--   Residue Extension: exists completion
-- statement:
--   The Residue Extension construction uses the exists completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L140-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsCompleteDiscreteValuationRingWithResidues.lean#L140-L153

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

theorem GlobalTheory.ResidueExtension.exists_completion (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) :
    ∃ r' : AdicCompletion (maximalIdeal O) O →+* Ω,
      r'.comp (algebraMap O _) = r ∧ RingHom.ker r' = maximalIdeal _ := by sorry
