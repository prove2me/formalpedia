-- Prove2me | Theorems.Thm_GlobalTheory_trace_tensorProduct_map_complex
-- name    : GlobalTheory.trace_tensorProduct_map_complex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:15.967633+00:00
-- url     : https://prove2.me/theorems/a1583551-2a41-591e-a35f-e3cf265a1364
-- title:
--   Global Theory: trace tensor Product map complex
-- statement:
--   The Global Theory construction uses the trace tensor Product map complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteLeftOfFiniteTensorProductComplex.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteLeftOfFiniteTensorProductComplex.lean#L38-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteLeftOfFiniteTensorProductComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open scoped TensorProduct

theorem GlobalTheory.trace_tensorProduct_map_complex {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by sorry
