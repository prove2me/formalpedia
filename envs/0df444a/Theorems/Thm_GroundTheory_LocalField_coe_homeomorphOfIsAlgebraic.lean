-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
-- name    : GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:43.679898+00:00
-- url     : https://prove2.me/theorems/d28356b7-d8c2-452e-9cf7-60fb67ba2935
-- title:
--   Local Field: coe homeomorph Of Is Algebraic
-- statement:
--   The Local Field construction uses the coe homeomorph Of Is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosure.lean#L369-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosure.lean#L369-L370

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter Polynomial
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω]
variable [Algebra.IsAlgebraic K Ω]

theorem GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic (σ : Ω ≃ₐ[K] Ω) : ⇑(homeomorphOfIsAlgebraic σ) = σ := by sorry

attribute [defeq] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
