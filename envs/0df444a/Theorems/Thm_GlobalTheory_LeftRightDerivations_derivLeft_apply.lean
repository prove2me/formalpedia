-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_derivLeft_apply
-- name    : GlobalTheory.LeftRightDerivations.derivLeft_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:53.702182+00:00
-- url     : https://prove2.me/theorems/2ffc6481-29d1-4d0b-ac53-a81733d06533
-- title:
--   Left Right Derivations: deriv Left apply
-- statement:
--   The Left Right Derivations construction uses the deriv Left apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L125-L127

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

theorem GlobalTheory.LeftRightDerivations.derivLeft_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivLeft φ hφ y =
      TensorProduct.lid k H (LinearMap.rTensor H φ (Coalgebra.comul (R := k) y)) := by sorry
