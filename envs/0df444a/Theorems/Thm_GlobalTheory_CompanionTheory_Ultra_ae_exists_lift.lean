-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_exists_lift
-- name    : GlobalTheory.CompanionTheory.Ultra.ae_exists_lift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:21.473884+00:00
-- url     : https://prove2.me/theorems/eb6b76a2-e750-45e4-9705-ec7d332f99c4
-- title:
--   Ultra: ae exists lift
-- statement:
--   The Ultra construction uses the ae exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L147-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L147-L189

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
variable {f₀}
variable (f₀)
variable {ι : Type} (U : Ultrafilter ι) {T V K : ι → Type} [∀ i, CommRing (T i)]
  [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)] [∀ i, IsFractionRing (V i) (K i)]
  (ψ : ∀ i, R₀ →+* T i)
  (a : ∀ i, Spec (CommRingCat.of (K i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))))
  (β : ∀ i, T i →+* V i)

theorem GlobalTheory.CompanionTheory.Ultra.ae_exists_lift [CompactSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∀ᶠ i in (U : Filter ι), ∃ l : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))),
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) := by sorry
