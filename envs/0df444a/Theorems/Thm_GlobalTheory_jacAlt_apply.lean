-- Prove2me | Theorems.Thm_GlobalTheory_jacAlt_apply
-- name    : GlobalTheory.jacAlt_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:06.920027+00:00
-- url     : https://prove2.me/theorems/1f476866-a3eb-4858-bde6-678ce1498191
-- title:
--   Global Theory: jac Alt apply
-- statement:
--   The Global Theory construction uses the jac Alt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L234-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L234-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential

theorem GlobalTheory.jacAlt_apply (f : Fin (D + 1) → A) : jacobianMultilinear R A D f = jac R f := by sorry
