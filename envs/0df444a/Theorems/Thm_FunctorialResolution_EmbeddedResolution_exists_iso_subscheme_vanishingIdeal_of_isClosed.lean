-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_iso_subscheme_vanishingIdeal_of_isClosed
-- name    : FunctorialResolution.EmbeddedResolution.exists_iso_subscheme_vanishingIdeal_of_isClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:45.798851+00:00
-- url     : https://prove2.me/theorems/e8e37e6e-e471-48bd-9431-c022275a78f2
-- title:
--   Embedded Resolution: exists iso subscheme vanishing Ideal of is Closed
-- statement:
--   The Embedded Resolution construction uses the exists iso subscheme vanishing Ideal of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/ClopenSubscheme.lean#L73-L80

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

theorem FunctorialResolution.EmbeddedResolution.exists_iso_subscheme_vanishingIdeal_of_isClosed
    {X : Scheme} [IsReduced X] (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal
        (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι =
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subschemeι := by sorry
