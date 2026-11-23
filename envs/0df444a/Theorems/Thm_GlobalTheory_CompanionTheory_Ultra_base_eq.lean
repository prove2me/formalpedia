-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_base_eq
-- name    : GlobalTheory.CompanionTheory.Ultra.base_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:31.066976+00:00
-- url     : https://prove2.me/theorems/8e62be1b-7ea7-4158-8994-bac8a27c9f27
-- title:
--   Ultra: base eq
-- statement:
--   The Ultra construction uses the base eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L38-L45

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

theorem GlobalTheory.CompanionTheory.Ultra.base_eq {T A : Type} [CommRing T] [CommRing A] (ψ : R₀ →+* T) (W : X.affineOpens)
    (p : Γ(X, W.1) →+* A) (t : T →+* A)
    (l : Spec (CommRingCat.of A) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h1 : l ≫ pullback.fst _ _ = pt W p)
    (h2 : l ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom t)) :
    p.comp (baseHom f₀ W) = t.comp ψ := by sorry
