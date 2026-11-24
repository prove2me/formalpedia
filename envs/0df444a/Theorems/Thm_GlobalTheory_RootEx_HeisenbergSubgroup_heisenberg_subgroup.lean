-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_heisenberg_subgroup
-- name    : GlobalTheory.RootEx.HeisenbergSubgroup.heisenberg_subgroup
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:53.564354+00:00
-- url     : https://prove2.me/theorems/c9c96b29-6470-4c9d-857d-737df8c2e523
-- title:
--   Heisenberg Subgroup: heisenberg subgroup
-- statement:
--   The Heisenberg Subgroup construction uses the heisenberg subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsHeisenbergSubgroupFourierJacobiCommutator.lean#L173-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsHeisenbergSubgroupFourierJacobiCommutator.lean#L173-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSubgroup

theorem GlobalTheory.RootEx.HeisenbergSubgroup.heisenberg_subgroup : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k), g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧ ∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val = cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val := by sorry
