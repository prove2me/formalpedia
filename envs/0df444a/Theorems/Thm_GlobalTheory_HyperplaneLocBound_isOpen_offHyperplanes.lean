-- Prove2me | Theorems.Thm_GlobalTheory_HyperplaneLocBound_isOpen_offHyperplanes
-- name    : GlobalTheory.HyperplaneLocBound.isOpen_offHyperplanes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:58.857793+00:00
-- url     : https://prove2.me/theorems/7361dba8-6eea-43c6-b1d4-c3251585ecf6
-- title:
--   Hyperplane Loc Bound: is Open off Hyperplanes
-- statement:
--   The Hyperplane Loc Bound construction uses the is Open off Hyperplanes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocallyBoundedOffCoordinateHyperplanes.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocallyBoundedOffCoordinateHyperplanes.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.HyperplaneLocBound

theorem GlobalTheory.HyperplaneLocBound.isOpen_offHyperplanes (n a : ℕ) (ρ : ℝ) :
    IsOpen {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by sorry
