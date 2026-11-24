-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_limit_lift
-- name    : GlobalTheory.CompanionTheory.Ultra.limit_lift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:43.114252+00:00
-- url     : https://prove2.me/theorems/5b3da12c-14fd-4de9-bdfa-7e8ea2788f0b
-- title:
--   Ultra: limit lift
-- statement:
--   The Ultra construction uses the limit lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L191-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L191-L216

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

theorem GlobalTheory.CompanionTheory.Ultra.limit_lift [QuasiSeparatedSpace X] {φ : R₀ →+* R}
    (ρ : R →+* Ult U V) (hρ : ∀ r, ρ (φ r) = mk U (fun i => β i (ψ i r)))
    {W W₁ : X.affineOpens} {h : ∀ i, Γ(X, W.1) → V i} {G : Γ(X, W.1) →+* Ult U V} (r : Rep U h G)
    {h₁ : ∀ i, Γ(X, W₁.1) → K i} {P : Γ(X, W₁.1) →+* Ult U K} (rP : Rep U h₁ P)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W.1) →+* V i) (q : Γ(X, W₁.1) →+* K i)
      (l : Spec (CommRingCat.of (V i)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (ψ i)))),
      ⇑p = h i ∧ ⇑q = h₁ i ∧ l ≫ pullback.fst _ _ = pt W p ∧
      l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (β i)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (V i) (K i))) ≫ l = a i ∧
      a i ≫ pullback.fst _ _ = pt W₁ q) :
    pt W G ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
    Spec.map (CommRingCat.ofHom (algebraMap (Ult U V) (Ult U K))) ≫ pt W G = pt W₁ P := by sorry
