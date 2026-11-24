-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_basicOpen
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_basicOpen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:40.357777+00:00
-- url     : https://prove2.me/theorems/d4f0d3a5-314d-4a75-9c49-16d75b037706
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections basic Open
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L113-L119

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_basicOpen (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec (CommRingCat.of (MvPolynomial v k))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := by sorry
