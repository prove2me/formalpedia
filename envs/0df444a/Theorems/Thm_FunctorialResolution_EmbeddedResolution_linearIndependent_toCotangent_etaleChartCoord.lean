-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_toCotangent_etaleChartCoord
-- name    : FunctorialResolution.EmbeddedResolution.linearIndependent_toCotangent_etaleChartCoord
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:29:04.546272+00:00
-- url     : https://prove2.me/theorems/14c1de62-a1ca-4f08-8d2f-f28817978d44
-- title:
--   Embedded Resolution: linear Independent to Cotangent etale Chart Coord
-- statement:
--   The Embedded Resolution construction uses the linear Independent to Cotangent etale Chart Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorRadical.lean#L98-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateDivisorRadical.lean#L98-L195

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.linearIndependent_toCotangent_etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q)
    (hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j : { x : Fin m // x ∈ J } =>
          (IsLocalRing.maximalIdeal A).toCotangent
            ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :
        { x : Fin m // x ∈ J } → IsLocalRing.CotangentSpace A) := by sorry
