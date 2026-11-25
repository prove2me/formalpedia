-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_isCounitDerivation_iff
-- name    : GlobalTheory.LeftRightDerivations.isCounitDerivation_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:22.605606+00:00
-- url     : https://prove2.me/theorems/3555a0f8-203c-4bb1-af61-83059b6b33e7
-- title:
--   Left Right Derivations: is Counit Derivation iff
-- statement:
--   The Left Right Derivations construction uses the is Counit Derivation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L13-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LeftRightDerivations
variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

theorem GlobalTheory.LeftRightDerivations.isCounitDerivation_iff (φ : H →ₗ[k] k) :
    IsCounitDerivation φ ↔ ∀ a b : H, φ (a * b) =
      Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a := by sorry
