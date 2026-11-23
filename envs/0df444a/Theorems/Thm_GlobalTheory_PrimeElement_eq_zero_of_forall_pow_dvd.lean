-- Prove2me | Theorems.Thm_GlobalTheory_PrimeElement_eq_zero_of_forall_pow_dvd
-- name    : GlobalTheory.PrimeElement.eq_zero_of_forall_pow_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:39.170911+00:00
-- url     : https://prove2.me/theorems/d6739d9f-0263-415a-9401-ccb1f7941cd1
-- title:
--   Prime Element: eq zero of forall pow dvd
-- statement:
--   The Prime Element construction uses the eq zero of forall pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}

theorem GlobalTheory.PrimeElement.eq_zero_of_forall_pow_dvd [IsDomain R] [IsNoetherianRing R] (hπ : ¬ IsUnit π) {x : R}
    (hx : ∀ e : ℕ, π ^ e ∣ x) : x = 0 := by sorry
