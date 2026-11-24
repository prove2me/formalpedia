-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_apply
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:17.638821+00:00
-- url     : https://prove2.me/theorems/6b29b0f3-1422-487e-8d65-c948ca0a551a
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections symm apply
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L73-L77

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := by sorry
