-- Prove2me | Theorems.Thm_GlobalTheory_LeftRightDerivations_isCounitDerivation_counit_comp
-- name    : GlobalTheory.LeftRightDerivations.isCounitDerivation_counit_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:10.875686+00:00
-- url     : https://prove2.me/theorems/7c7a8a52-190d-564f-8d54-486fb589da14
-- title:
--   Left Right Derivations: is Counit Derivation counit comp
-- statement:
--   The Left Right Derivations construction uses the is Counit Derivation counit comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsCounitDerivationCounitComp.lean#L139-L143

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

theorem GlobalTheory.LeftRightDerivations.isCounitDerivation_counit_comp (D : Derivation k H H) :
    IsCounitDerivation (Coalgebra.counit (R := k) ∘ₗ D.toLinearMap) := by sorry
