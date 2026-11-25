-- Prove2me | Theorems.Thm_GlobalTheory_PlaceTransport_intValuation_comap_equiv
-- name    : GlobalTheory.PlaceTransport.intValuation_comap_equiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:17.287703+00:00
-- url     : https://prove2.me/theorems/c62b6834-ea44-48e3-a1ee-348d7246414b
-- title:
--   Place Transport: int Valuation comap equiv
-- statement:
--   The Place Transport construction uses the int Valuation comap equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinitePlaceValuationCompRingEquiv.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFinitePlaceValuationCompRingEquiv.lean#L22-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinitePlaceValuationCompRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.PlaceTransport

theorem GlobalTheory.PlaceTransport.intValuation_comap_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by sorry
