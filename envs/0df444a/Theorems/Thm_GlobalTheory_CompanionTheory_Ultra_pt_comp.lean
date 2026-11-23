-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_comp
-- name    : GlobalTheory.CompanionTheory.Ultra.pt_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:23.793147+00:00
-- url     : https://prove2.me/theorems/32e6c4f5-d1a8-4622-bf7c-f50c9329c295
-- title:
--   Ultra: pt comp
-- statement:
--   The Ultra construction uses the pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L34-L36

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

theorem GlobalTheory.CompanionTheory.Ultra.pt_comp (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A) :
    pt W p ≫ f₀ = Spec.map (CommRingCat.ofHom (p.comp (baseHom f₀ W))) := by sorry
