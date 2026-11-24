-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complOpensOfIsClosed
-- name    : FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:40.070037+00:00
-- url     : https://prove2.me/theorems/850ec830-6a38-4c58-ae2c-5912b9aaf108
-- title:
--   Embedded Resolution: coe compl Opens Of Is Closed
-- statement:
--   The Embedded Resolution construction uses the coe compl Opens Of Is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean#L86-L87

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed {X : Scheme} (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ((complOpensOfIsClosed C hC : X.Opens) : Set X) = (C : Set X)ᶜ := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed
