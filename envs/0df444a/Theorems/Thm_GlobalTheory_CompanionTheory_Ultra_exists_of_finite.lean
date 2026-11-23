-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_of_finite
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_of_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:19.11102+00:00
-- url     : https://prove2.me/theorems/8be0e1af-c447-454e-b18f-882a27d97c05
-- title:
--   Ultra: exists of finite
-- statement:
--   The Ultra construction uses the exists of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L334-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L334-L341

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
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
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.Ultra.exists_of_finite {α : Type} {S : Set α} (hS : S.Finite) {Q : α → ι → Prop}
    (H : ∀ᶠ i in (U : Filter ι), ∃ W ∈ S, Q W i) : ∃ W ∈ S, ∀ᶠ i in (U : Filter ι), Q W i := by sorry
