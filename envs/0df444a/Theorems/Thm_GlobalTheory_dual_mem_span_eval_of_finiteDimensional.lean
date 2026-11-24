-- Prove2me | Theorems.Thm_GlobalTheory_dual_mem_span_eval_of_finiteDimensional
-- name    : GlobalTheory.dual_mem_span_eval_of_finiteDimensional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:59.815796+00:00
-- url     : https://prove2.me/theorems/573cfb85-fb5e-4c97-a799-d792c8b846e2
-- title:
--   Global Theory: dual mem span eval of finite Dimensional
-- statement:
--   The Global Theory construction uses the dual mem span eval of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMemFinDimSubspace.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMemFinDimSubspace.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualMemSpanEvalOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMemFinDimSubspace
import Theorems.Thm_UpperTheory_Reformulated_B_Yyc2_dual_mem_span_eval_of_finiteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.dual_mem_span_eval_of_finiteDimensional {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) := by sorry
