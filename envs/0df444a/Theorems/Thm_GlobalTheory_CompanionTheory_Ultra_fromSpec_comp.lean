-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_fromSpec_comp
-- name    : GlobalTheory.CompanionTheory.Ultra.fromSpec_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:38.404849+00:00
-- url     : https://prove2.me/theorems/b1b3ebfc-b326-4416-95b8-c237015b19aa
-- title:
--   Ultra: from Spec comp
-- statement:
--   The Ultra construction uses the from Spec comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L21-L23

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

theorem GlobalTheory.CompanionTheory.Ultra.fromSpec_comp (W : X.affineOpens) :
    W.2.fromSpec ≫ f₀ = Spec.map (CommRingCat.ofHom (baseHom f₀ W)) := by sorry
