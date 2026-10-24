-- Prove2me | Theorems.Thm_OAI_PiExponent_eventualLogJetSurjective_transverseForSpatialVolume_360483bd
-- name    : OAI.PiExponent.eventualLogJetSurjective_transverseForSpatialVolume_360483bd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T17:28:40.617371+00:00
-- url     : https://prove2.me/theorems/9b7e8bd1-5d55-4329-9655-cbdd8e23d0a9
-- title:
--   Restrict logarithmic interpolation to transverse jets
-- statement:
--   Specialize the logarithmic interpolation property to logarithmic exponent zero. The truncated logarithm has zero constant term, so restriction to that slice gives the stated transverse interpolation property with the same source and target cutoffs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_eventualTransverseJetSurjectiveForSpatialVolume_360483bd
open scoped BigOperators

theorem OAI.PiExponent.eventualLogJetSurjective_transverseForSpatialVolume_360483bd
    (m K : Nat) (w0 v0 alpha : Rat)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (halpha : 0 < alpha)
    (w : Fin m → Nat) (hw : ∀ i, 0 < w i)
    (c : Fin K → Fin m → Complex)
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    OAI.PiExponent.eventualTransverseJetSurjectiveForSpatialVolume_360483bd m K alpha w c := by sorry
