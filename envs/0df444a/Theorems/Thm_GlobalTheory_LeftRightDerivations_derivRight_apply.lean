-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_derivRight_apply
-- name    : GlobalTheory.LeftRightDerivations.derivRight_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:47.982505+00:00
-- url     : https://prove2.me/theorems/adf5e68f-ec57-45c4-831a-495ed25fbf62
-- title:
--   Left Right Derivations: deriv Right apply
-- statement:
--   The Left Right Derivations construction uses the deriv Right apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L121-L123

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
variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

theorem GlobalTheory.LeftRightDerivations.derivRight_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivRight φ hφ y =
      TensorProduct.rid k H (LinearMap.lTensor H φ (Coalgebra.comul (R := k) y)) := by sorry
