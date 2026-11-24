-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_prod_eq
-- name    : GlobalTheory.RootEx.HeisenbergSubgroup.prod_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:26:30.526077+00:00
-- url     : https://prove2.me/theorems/4b0d4f58-aa39-4bd1-abac-a152c33bc9fb
-- title:
--   Heisenberg Subgroup: prod eq
-- statement:
--   The Heisenberg Subgroup construction uses the prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsHeisenbergSubgroupFourierJacobiCommutator.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsHeisenbergSubgroupFourierJacobiCommutator.lean#L106-L109

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
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootEx.HeisenbergSubgroup.prod_eq (u β : n → k) (t : k) :
    (rowE c p u).val * (colE c (p + 1) β).val * cenM n c p t = hM c p u β (u ⬝ᵥ β + t) := by sorry
