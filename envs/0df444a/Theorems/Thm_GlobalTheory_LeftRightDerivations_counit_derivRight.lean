-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_counit_derivRight
-- name    : GlobalTheory.LeftRightDerivations.counit_derivRight
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:20.061769+00:00
-- url     : https://prove2.me/theorems/7d6b2da3-89b3-4bb2-a36e-70f2fd52c507
-- title:
--   Left Right Derivations: counit deriv Right
-- statement:
--   The Left Right Derivations construction uses the counit deriv Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L129-L132

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

theorem GlobalTheory.LeftRightDerivations.counit_derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivRight φ hφ y) = φ y := by sorry
