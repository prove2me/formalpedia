-- Prove2me | Theorems.Thm_GlobalTheory_polyDerivLinear_apply
-- name    : GlobalTheory.polyDerivLinear_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:17.131125+00:00
-- url     : https://prove2.me/theorems/3ee35d72-551b-4449-9e57-c18c8da84d47
-- title:
--   Global Theory: poly Deriv Linear apply
-- statement:
--   The Global Theory construction uses the poly Deriv Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L80-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem GlobalTheory.polyDerivLinear_apply (F : (ι → 𝕜) → V) (a : ι → 𝕜) (P : MvPolynomial ι 𝕜) :
    polyDerivLinear F a P = polyDeriv P F a := by sorry

attribute [defeq] GlobalTheory.polyDerivLinear_apply
