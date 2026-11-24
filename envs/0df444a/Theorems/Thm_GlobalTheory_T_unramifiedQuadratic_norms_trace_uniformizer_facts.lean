-- Prove2me | Theorems.Thm_GlobalTheory_T_unramifiedQuadratic_norms_trace_uniformizer_facts
-- name    : GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:00:36.759+00:00
-- url     : https://prove2.me/theorems/5244bdb0-ba9f-43da-a75f-ae4a4997dd4d
-- title:
--   T: unramified Quadratic norms trace uniformizer facts
-- statement:
--   The T construction uses the unramified Quadratic norms trace uniformizer facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFactsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFactsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFactsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts : ∀ (K : UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u → ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧ (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧ (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧ ∀ x : K.E, val K.O (K.c x) = val K.O x := by sorry
