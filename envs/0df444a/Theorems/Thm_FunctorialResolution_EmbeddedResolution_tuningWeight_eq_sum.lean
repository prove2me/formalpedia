-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_eq_sum
-- name    : FunctorialResolution.EmbeddedResolution.tuningWeight_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:14.118416+00:00
-- url     : https://prove2.me/theorems/a6b17798-eaf5-4d56-b978-92a06840f1ae
-- title:
--   Embedded Resolution: tuning Weight eq sum
-- statement:
--   The Embedded Resolution construction uses the tuning Weight eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L8-L9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.tuningWeight_eq_sum (m : ℕ) (c : ℕ → ℕ) :
    tuningWeight m c = ∑ j ∈ Finset.range m, (m - j) * c j := by sorry
