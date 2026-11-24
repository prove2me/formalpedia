-- Prove2me | Theorems.Thm_GlobalTheory_T_associated_prime_localization_dvr
-- name    : GlobalTheory.T.associated_prime_localization_dvr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:54.190067+00:00
-- url     : https://prove2.me/theorems/599b3b35-9133-42d5-ba6e-6a0911a3c3b9
-- title:
--   T: associated prime localization dvr
-- statement:
--   The T construction uses the associated prime localization dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvrStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvrStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.associated_prime_localization_dvr : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 → (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) → ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by sorry
