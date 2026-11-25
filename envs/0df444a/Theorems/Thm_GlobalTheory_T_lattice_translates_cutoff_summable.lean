-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_translates_cutoff_summable
-- name    : GlobalTheory.T.lattice_translates_cutoff_summable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:16.634611+00:00
-- url     : https://prove2.me/theorems/89af9eff-23ee-4d3f-a028-199ba804f087
-- title:
--   T: lattice translates cutoff summable
-- statement:
--   The T construction uses the lattice translates cutoff summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeTranslatesCutoffSummableStatement.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeTranslatesCutoffSummableStatement.lean#L5-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_translates_cutoff_summable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h (x + l) * f x) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by sorry
