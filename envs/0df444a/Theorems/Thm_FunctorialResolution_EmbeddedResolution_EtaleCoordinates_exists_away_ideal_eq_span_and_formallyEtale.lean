-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_away_ideal_eq_span_and_formallyEtale
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_ideal_eq_span_and_formallyEtale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:51.932282+00:00
-- url     : https://prove2.me/theorems/5f5ea3d1-820d-464e-8a27-712bb5c58c8b
-- title:
--   Etale Coordinates: exists away ideal eq span and formally Etale
-- statement:
--   The Etale Coordinates construction uses the exists away ideal eq span and formally Etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalNormalForm.lean#L595-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalNormalForm.lean#L595-L615

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_ideal_eq_span_and_formallyEtale
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
      @Algebra.FormallyEtale (MvPolynomial ι k) (Localization.Away g) _ _
        (RingHom.toAlgebra
          (MvPolynomial.eval₂Hom
            ((algebraMap S (Localization.Away g)).comp (algebraMap k S))
            (fun j : ι => algebraMap S (Localization.Away g) (w j)))) := by sorry
