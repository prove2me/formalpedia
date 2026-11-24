-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
-- name    : FunctorialResolution.EmbeddedResolution.derivIdeal_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:51.550825+00:00
-- url     : https://prove2.me/theorems/8784da82-4e4c-4c95-a664-f14ad2bac75a
-- title:
--   Embedded Resolution: deriv Ideal le iff
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L38-L48

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.derivIdeal_le_iff (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J K : Ideal S) :
    derivIdeal k J ≤ K ↔ J ≤ K ∧ ∀ D : Derivation k S S, ∀ x ∈ J, D x ∈ K := by sorry
