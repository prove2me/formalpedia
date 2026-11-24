-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_formallyEtale_trans
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.formallyEtale_trans
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:55.208121+00:00
-- url     : https://prove2.me/theorems/ecdde7a6-4963-49e4-b483-b49a1b3b1765
-- title:
--   Etale Coordinates: formally Etale trans
-- statement:
--   The Etale Coordinates construction uses the formally Etale trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L227-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/PolynomialCoordinateExtension.lean#L227-L234

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
open MvPolynomial
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra
variable (T : Type*) [CommRing T]

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.formallyEtale_trans [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra (MvPolynomial κ S) T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial κ S) T] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T := by sorry
