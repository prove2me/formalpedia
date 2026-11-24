-- Prove2me | Theorems.Thm_GlobalTheory_monoToQuotPow_mk
-- name    : GlobalTheory.monoToQuotPow_mk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:31.439083+00:00
-- url     : https://prove2.me/theorems/91a10e79-5ec4-4bce-b5f4-5831a4ffaee2
-- title:
--   Global Theory: mono To Quot Pow mk
-- statement:
--   The Global Theory construction uses the mono To Quot Pow mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L521-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L521-L525

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

theorem GlobalTheory.monoToQuotPow_mk (f : ι → R) (a : ℕ) (c : MonoDeg ι a → R) :
    monoToQuotPow f a (fun α => Ideal.Quotient.mk _ (c α)) =
      Ideal.Quotient.mk _ (∑ α, monoVal f α.1 * c α) := by sorry
