-- Prove2me | Theorems.Thm_GlobalTheory_T_weil_action_level_supNorm_uniform_in_lattice
-- name    : GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:04.616774+00:00
-- url     : https://prove2.me/theorems/7dc43909-4edb-4ae0-b29b-184f1be56ae0
-- title:
--   T: weil action level sup Norm uniform in lattice
-- statement:
--   The T construction uses the weil action level sup Norm uniform in lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLatticeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLatticeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → 0 < R → ∃ (R' : ℕ) (C : ℝ), 0 < R' ∧ ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, ∀ γ ∈ UU E N, Den c γ → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R φ → IsSB φ ∧ LevelL Λ R' (weil Ψ γ φ) ∧ ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ x, ‖weil Ψ γ φ x‖ ≤ C * B := by sorry
