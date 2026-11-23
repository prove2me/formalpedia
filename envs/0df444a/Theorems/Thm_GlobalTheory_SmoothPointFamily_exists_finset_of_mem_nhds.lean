-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_finset_of_mem_nhds
-- name    : GlobalTheory.SmoothPointFamily.exists_finset_of_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:14.149878+00:00
-- url     : https://prove2.me/theorems/db69e345-658c-4377-8c51-a3eba26a4cab
-- title:
--   Smooth Point Family: exists finset of mem nhds
-- statement:
--   The Smooth Point Family construction uses the exists finset of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsHolomorphicFamily.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsHolomorphicFamily.lean#L70-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.SmoothPointFamily
open KaehlerDifferential

theorem GlobalTheory.SmoothPointFamily.exists_finset_of_mem_nhds {A : Type} {x : A → ℂ} {U : Set (A → ℂ)} (hU : U ∈ 𝓝 x) :
    ∃ (S : Finset A) (ε : ℝ), 0 < ε ∧ ∀ y : A → ℂ, (∀ a ∈ S, ‖y a - x a‖ < ε) → y ∈ U := by sorry
