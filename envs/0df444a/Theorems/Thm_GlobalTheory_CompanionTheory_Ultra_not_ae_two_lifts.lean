-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_not_ae_two_lifts
-- name    : GlobalTheory.CompanionTheory.Ultra.not_ae_two_lifts
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:28.181295+00:00
-- url     : https://prove2.me/theorems/4aa71153-2ebe-4061-9a33-d789939b4ca5
-- title:
--   Ultra: not ae two lifts
-- statement:
--   The Ultra construction uses the not ae two lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L218-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L218-L285

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

theorem GlobalTheory.CompanionTheory.Ultra.not_ae_two_lifts [CompactSpace X] [QuasiSeparatedSpace X] [Algebra.FiniteType ℤ R₀]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    (H : ∀ᶠ i in (U : Filter ι), ∃ l₁ l₂ : Spec (CommRingCat.of (V i)) ⟶
        pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i))), l₁ ≠ l₂ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₁ = a i ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l₂ = a i ∧
      l₁ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      l₂ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i))) : False := by sorry
