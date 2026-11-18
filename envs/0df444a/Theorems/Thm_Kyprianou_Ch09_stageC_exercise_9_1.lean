-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_exercise_9_1
-- name    : Kyprianou.Ch09.stageC_exercise_9_1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:46:16.969021+00:00
-- url     : https://prove2.me/theorems/c935cf87-5c21-472c-af7d-99eb962d22d4
-- title:
--   Exercise 9.1: complete three-part optimal stopping problem
-- statement:
--   Exercise 9.1. Model and parameter assumptions: X any Lévy process; q>0 OR q=0 AND X_t→−∞ a.s. (distinct from Theorem 9.2), T all ℱ-stopping times; supremum overline X_(e_q). Quantifiers and stopping-time domain: All initial x∈ℝ and a>0 for (i); all x for (ii) and fit test (iii). Mathematical assertion: (i) E_x[e^(−qT_a⁺)(1−e^(−X_(T_a⁺)))1_{T_a⁺<∞}]=E_x[(1−e^(−overline X_(e_q))/E[e^(−overline X_(e_q))])1_{overline X_(e_q)≥a}]; (ii) x* solves e^(−x*)=E[e^(−overline X_(e_q))], value from (i) with a=x*, τ*=T_(x*)⁺; (iii) smooth fit iff 0 upward regular, otherwise continuous fit. Source clarification: Full exercise (i)–(iii) unchanged. Author solution printed p.353/PDF 359 incorrectly says 'irregular' in its last sentence; correction applies only to solution prose. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Exercise 9.1; original PDF pp. [277]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_exercise_9_1 :
  exercise9_1_i ∧ exercise9_1_ii ∧ exercise9_1_iii := by
  sorry

end Kyprianou.Ch09
