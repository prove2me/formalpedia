-- Prove2me | Theorems.Thm_GlobalTheory_finite_quotSMulTop_ker_of_regular
-- name    : GlobalTheory.finite_quotSMulTop_ker_of_regular
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:10.963092+00:00
-- url     : https://prove2.me/theorems/749f6ac7-538d-4fb8-8a7b-86903c373c10
-- title:
--   Global Theory: finite quot SMul Top ker of regular
-- statement:
--   The Global Theory construction uses the finite quot SMul Top ker of regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsPowSmulEqAddSubOneSmul.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsPowSmulEqAddSubOneSmul.lean#L63-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowSmulEqAddSubOneSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.finite_quotSMulTop_ker_of_regular {S F G : Type} [CommRing S] [AddCommGroup F]
    [Module S F] [AddCommGroup G] [Module S G] (u : S) (φ : F →ₗ[S] G)
    (hreg : ∀ z : G, u • z = 0 → z = 0) [Module.Finite S F]
    [Module.FinitePresentation S (QuotSMulTop u G)]
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), φ y = z + u • w)
    (hker : ∀ (y : F) (w : G), φ y = u • w → ∃ (k v : F), φ k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker φ)) := by sorry
