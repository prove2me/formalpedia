-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_comap_eq
-- name    : FunctorialResolution.EmbeddedResolution.support_comap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:46.275148+00:00
-- url     : https://prove2.me/theorems/7c264b4b-3f32-4608-a3db-70603e5b51be
-- title:
--   Embedded Resolution: support comap eq
-- statement:
--   The Embedded Resolution construction uses the support comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L125-L128

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry

theorem FunctorialResolution.EmbeddedResolution.support_comap_eq {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) := by sorry
