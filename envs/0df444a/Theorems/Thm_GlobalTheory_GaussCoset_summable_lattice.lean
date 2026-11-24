-- Prove2me | Theorems.Thm_GlobalTheory_GaussCoset_summable_lattice
-- name    : GlobalTheory.GaussCoset.summable_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:03.755199+00:00
-- url     : https://prove2.me/theorems/8c4a22e6-74eb-4e4e-9287-0d5e54ed5616
-- title:
--   Gauss Coset: summable lattice
-- statement:
--   The Gauss Coset construction uses the summable lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L29-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset

theorem GlobalTheory.GaussCoset.summable_lattice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ} (hc : 0 < c)
    (R : ℝ) (x : V) :
    Summable fun z : L => Real.exp (-c * ‖(z : V) - x‖ ^ 2 + R * ‖(z : V) - x‖) := by sorry
