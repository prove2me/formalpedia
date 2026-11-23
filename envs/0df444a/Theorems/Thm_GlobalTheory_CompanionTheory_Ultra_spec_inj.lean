-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_spec_inj
-- name    : GlobalTheory.CompanionTheory.Ultra.spec_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:55.320288+00:00
-- url     : https://prove2.me/theorems/5f4546c5-ffc7-499b-b3b3-6314f38d0f67
-- title:
--   Ultra: spec inj
-- statement:
--   The Ultra construction uses the spec inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L30-L32

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

theorem GlobalTheory.CompanionTheory.Ultra.spec_inj {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B}
    (h : Spec.map (CommRingCat.ofHom p) = Spec.map (CommRingCat.ofHom q)) : p = q := by sorry
