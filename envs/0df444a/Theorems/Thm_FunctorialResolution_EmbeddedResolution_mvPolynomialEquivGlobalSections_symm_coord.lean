-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_coord
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:02.680065+00:00
-- url     : https://prove2.me/theorems/add830af-377a-4ae6-bda0-7cf4933adc76
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections symm coord
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections symm coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L90-L93

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (mvPolynomialEquivGlobalSections k v).symm (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      MvPolynomial.X i := by sorry
