-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_limit_point
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_limit_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:40.863591+00:00
-- url     : https://prove2.me/theorems/bc2af5e1-61b1-45ea-858f-530650a15e5c
-- title:
--   Ultra: exists limit point
-- statement:
--   The Ultra construction uses the exists limit point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L117-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L117-L145

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

theorem GlobalTheory.CompanionTheory.Ultra.exists_limit_point [CompactSpace X] (φ : R₀ →+* R)
    (hsq : ∀ i, a i ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((algebraMap (V i) (K i)).comp (β i))))
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r))) :
    ∃ (W₁ : X.affineOpens) (h₁ : ∀ i, Γ(X, W₁.1) → K i) (P : Γ(X, W₁.1) →+* Ult U K),
      Rep U h₁ P ∧
      (∀ᶠ i in (U : Filter ι), ∃ p : Γ(X, W₁.1) →+* K i, ⇑p = h₁ i ∧
        a i ≫ pullback.fst _ _ = pt W₁ p) ∧
      P.comp (baseHom f₀ W₁) = (algebraMap (Ult U V) (Ult U K)).comp (ρ.comp φ) := by sorry
