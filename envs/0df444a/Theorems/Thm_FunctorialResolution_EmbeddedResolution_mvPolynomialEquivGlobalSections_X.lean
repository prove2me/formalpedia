-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_X
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:55.663262+00:00
-- url     : https://prove2.me/theorems/b0987c7c-c062-43c0-90a4-4c4519196e60
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections X
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L85-L87

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (v : Type u) (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by sorry
