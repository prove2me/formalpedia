-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_C
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_C
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:19.991989+00:00
-- url     : https://prove2.me/theorems/2d716383-3845-488f-8fc1-d97eee8ea25b
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections C
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L95-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L95-L111

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (v : Type u) (c : k) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by sorry
