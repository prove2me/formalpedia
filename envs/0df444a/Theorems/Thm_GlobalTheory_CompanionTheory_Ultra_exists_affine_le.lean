-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_affine_le
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_affine_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:14.261597+00:00
-- url     : https://prove2.me/theorems/872fd6d3-80b1-4d4a-8087-7b6d79f7d310
-- title:
--   Ultra: exists affine le
-- statement:
--   The Ultra construction uses the exists affine le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L343-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L343-L346

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

theorem GlobalTheory.CompanionTheory.Ultra.exists_affine_le {O : X.Opens} {x : X} (hx : x ∈ O) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ W.1 ≤ O := by sorry
