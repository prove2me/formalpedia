-- Prove2me | Theorems.Thm_GlobalTheory_polyDeriv_zero_fun
-- name    : GlobalTheory.polyDeriv_zero_fun
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:10.925302+00:00
-- url     : https://prove2.me/theorems/ab265f11-bf79-4384-81cf-6a473132265e
-- title:
--   Global Theory: poly Deriv zero fun
-- statement:
--   The Global Theory construction uses the poly Deriv zero fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormPderivIterLeOfAnalyticAt.lean#L99-L101

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

theorem GlobalTheory.polyDeriv_zero_fun (P : MvPolynomial ι 𝕜) (a : ι → 𝕜) :
    polyDeriv P (fun _ => (0 : V)) a = 0 := by sorry
