-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_iSup_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdeal_iSup_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:30.615239+00:00
-- url     : https://prove2.me/theorems/1175e50b-5ea0-4a44-9423-ad49828ea517
-- title:
--   Embedded Resolution: deriv Ideal i Sup le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal i Sup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L73-L90

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

theorem FunctorialResolution.EmbeddedResolution.derivIdeal_iSup_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {ι : Sort*} (J : ι → Ideal S) :
    derivIdeal k (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) := by sorry
