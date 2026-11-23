-- Prove2me | Theorems.Thm_GlobalTheory_TriSqrt_det_eq_prod_diag
-- name    : GlobalTheory.TriSqrt.det_eq_prod_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:52.410589+00:00
-- url     : https://prove2.me/theorems/4e7a3476-6d61-48e3-8008-7872eff6b136
-- title:
--   Tri Sqrt: det eq prod diag
-- statement:
--   The Tri Sqrt construction uses the det eq prod diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrt.lean#L6-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrt.lean#L6-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContinuousOnNormDiagOfTriangularSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.TriSqrt

theorem GlobalTheory.TriSqrt.det_eq_prod_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by sorry
