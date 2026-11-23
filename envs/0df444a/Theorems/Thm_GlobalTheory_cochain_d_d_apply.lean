-- Prove2me | Theorems.Thm_GlobalTheory_cochain_d_d_apply
-- name    : GlobalTheory.cochain_d_d_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:18.562987+00:00
-- url     : https://prove2.me/theorems/90318cf9-39a6-48da-9864-c394cde7a29f
-- title:
--   Global Theory: cochain d d apply
-- statement:
--   The Global Theory construction uses the cochain d d apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L396-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L396-L397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]

theorem GlobalTheory.cochain_d_d_apply (K : CochainComplex (ModuleCat.{v} R) ℕ) (i j k : ℕ) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := by sorry
