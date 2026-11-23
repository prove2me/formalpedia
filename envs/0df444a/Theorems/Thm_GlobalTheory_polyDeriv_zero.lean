-- Prove2me | Theorems.Thm_GlobalTheory_polyDeriv_zero
-- name    : GlobalTheory.polyDeriv_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:11.816846+00:00
-- url     : https://prove2.me/theorems/5a23c18b-48f0-4b37-b4fe-a5bebb6f8ff0
-- title:
--   Global Theory: poly Deriv zero
-- statement:
--   The Global Theory construction uses the poly Deriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L83-L84

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

theorem GlobalTheory.polyDeriv_zero (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (0 : MvPolynomial ι 𝕜) F a = 0 := by sorry
