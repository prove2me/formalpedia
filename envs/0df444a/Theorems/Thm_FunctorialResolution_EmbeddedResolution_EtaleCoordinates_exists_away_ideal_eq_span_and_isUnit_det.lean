-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_away_ideal_eq_span_and_isUnit_det
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_ideal_eq_span_and_isUnit_det
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:15.372746+00:00
-- url     : https://prove2.me/theorems/220b32c1-cf66-492a-9438-b26a7cf0ffe7
-- title:
--   Etale Coordinates: exists away ideal eq span and is Unit det
-- statement:
--   The Etale Coordinates construction uses the exists away ideal eq span and is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalNormalForm.lean#L374-L593
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalNormalForm.lean#L374-L593

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealGeneratorsFromBase
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_ideal_eq_span_and_isUnit_det
    (A : Type*) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)]
    (hIq : I ≤ q) :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      IsUnit (algebraMap S (Localization.Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i))) := by sorry
