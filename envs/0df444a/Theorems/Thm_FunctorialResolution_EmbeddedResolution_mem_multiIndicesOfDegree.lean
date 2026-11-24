-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_multiIndicesOfDegree
-- name    : FunctorialResolution.EmbeddedResolution.mem_multiIndicesOfDegree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:41.647812+00:00
-- url     : https://prove2.me/theorems/6c516fdf-8141-49c7-afe0-bd5dba1ff3d2
-- title:
--   Embedded Resolution: mem multi Indices Of Degree
-- statement:
--   The Embedded Resolution construction uses the mem multi Indices Of Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LeadingForm.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LeadingForm.lean#L12-L22

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing

theorem FunctorialResolution.EmbeddedResolution.mem_multiIndicesOfDegree {h r : ℕ} (β : Fin h → ℕ) :
    β ∈ multiIndicesOfDegree h r ↔ ∑ i, β i = r := by sorry
