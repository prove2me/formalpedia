-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum
-- name    : FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:21.400065+00:00
-- url     : https://prove2.me/theorems/32e29789-2aa9-493e-ab05-53d181ab0a92
-- title:
--   Embedded Resolution: mv Polynomial Equiv Global Sections basic Open prime Spectrum
-- statement:
--   The Embedded Resolution construction uses the mv Polynomial Equiv Global Sections basic Open prime Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean#L121-L126

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

theorem FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens (PrimeSpectrum (MvPolynomial v k))) := by sorry
