-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_finiteType_lvl
-- name    : GlobalTheory.CompanionTheory.Ultra.finiteType_lvl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:12.80181+00:00
-- url     : https://prove2.me/theorems/c862baf7-03d4-460b-9f21-13d1d73208c3
-- title:
--   Ultra: finite Type lvl
-- statement:
--   The Ultra construction uses the finite Type lvl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L343-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L343-L346

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

theorem GlobalTheory.CompanionTheory.Ultra.finiteType_lvl {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {S₀ : Set R₀}
    (hS₀ : S₀.Finite) (F : Finset R) : Algebra.FiniteType ℤ (lvl φ S₀ F) := by sorry
