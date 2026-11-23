-- Prove2me | Theorems.Thm_GlobalTheory_polyDeriv_one
-- name    : GlobalTheory.polyDeriv_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:15.309832+00:00
-- url     : https://prove2.me/theorems/6e33d566-1ebc-4c99-b4a8-804f342d7adf
-- title:
--   Global Theory: poly Deriv one
-- statement:
--   The Global Theory construction uses the poly Deriv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L95-L97

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

theorem GlobalTheory.polyDeriv_one (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (1 : MvPolynomial ι 𝕜) F a = F a := by sorry
