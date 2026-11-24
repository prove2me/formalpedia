-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_fun_add
-- name    : FunctorialResolution.EmbeddedResolution.tuningWeight_fun_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:47.335733+00:00
-- url     : https://prove2.me/theorems/867edebf-6234-444a-9594-a2898edb3883
-- title:
--   Embedded Resolution: tuning Weight fun add
-- statement:
--   The Embedded Resolution construction uses the tuning Weight fun add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L11-L13

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

theorem FunctorialResolution.EmbeddedResolution.tuningWeight_fun_add (m : ℕ) (c d : ℕ → ℕ) :
    tuningWeight m (fun j => c j + d j) = tuningWeight m c + tuningWeight m d := by sorry
