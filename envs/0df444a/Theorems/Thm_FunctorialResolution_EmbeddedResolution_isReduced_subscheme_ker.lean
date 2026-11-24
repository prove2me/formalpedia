-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isReduced_subscheme_ker
-- name    : FunctorialResolution.EmbeddedResolution.isReduced_subscheme_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:41.276901+00:00
-- url     : https://prove2.me/theorems/3c294afa-baca-46ee-a801-1289da8b3f75
-- title:
--   Embedded Resolution: is Reduced subscheme ker
-- statement:
--   The Embedded Resolution construction uses the is Reduced subscheme ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ReducedSubscheme.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ReducedSubscheme.lean#L52-L58

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isReduced_subscheme_ker {W X : AlgebraicGeometry.Scheme}
    (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by sorry
