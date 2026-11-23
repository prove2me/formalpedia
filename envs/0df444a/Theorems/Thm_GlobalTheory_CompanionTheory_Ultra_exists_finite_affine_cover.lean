-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_finite_affine_cover
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_finite_affine_cover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:12.762806+00:00
-- url     : https://prove2.me/theorems/67d0ef44-4a5e-419e-9b79-7fc67f0bc549
-- title:
--   Ultra: exists finite affine cover
-- statement:
--   The Ultra construction uses the exists finite affine cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L348-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L348-L366

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

theorem GlobalTheory.CompanionTheory.Ultra.exists_finite_affine_cover (O : X.Opens) (hO : IsCompact (O : Set X)) :
    ∃ S : Set X.affineOpens, S.Finite ∧ (∀ W ∈ S, W.1 ≤ O) ∧ ∀ x ∈ O, ∃ W ∈ S, x ∈ W.1 := by sorry
