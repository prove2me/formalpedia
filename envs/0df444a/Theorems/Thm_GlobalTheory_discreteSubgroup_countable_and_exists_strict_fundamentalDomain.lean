-- Prove2me | Theorems.Thm_GlobalTheory_discreteSubgroup_countable_and_exists_strict_fundamentalDomain
-- name    : GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:56.611995+00:00
-- url     : https://prove2.me/theorems/8103ac30-2b65-49c6-af87-c6d48d181894
-- title:
--   Global Theory: discrete Subgroup countable and exists strict fundamental Domain
-- statement:
--   The Global Theory construction uses the discrete Subgroup countable and exists strict fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscreteSubgroupCountableAndExistsStrictFundamen.lean#L7-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscreteSubgroupCountableAndExistsStrictFundamen.lean#L7-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscreteSubgroupCountableAndExistsStrictFundamen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set TopologicalSpace
open GlobalTheory

theorem GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain : ∀ {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ],
    Countable Γ ∧ ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ D := by sorry
