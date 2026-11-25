-- Prove2me | Theorems.Thm_GlobalTheory_LatticeSchwartz_summable_seminorm_mul_comp_sub
-- name    : GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:32.691915+00:00
-- url     : https://prove2.me/theorems/f8864d3f-4505-4524-bd77-8e0a03bffc87
-- title:
--   Lattice Schwartz: summable seminorm mul comp sub
-- statement:
--   The Lattice Schwartz construction uses the summable seminorm mul comp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeShiftedCutoffSummable.lean#L48-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeShiftedCutoffSummable.lean#L48-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeShiftedCutoffSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeSchwartz

theorem GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by sorry
