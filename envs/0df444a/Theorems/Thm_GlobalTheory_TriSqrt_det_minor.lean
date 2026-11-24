-- Prove2me | Theorems.Thm_GlobalTheory_TriSqrt_det_minor
-- name    : GlobalTheory.TriSqrt.det_minor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:04.661895+00:00
-- url     : https://prove2.me/theorems/7ecc5ce1-7771-40d2-a4d1-9b05ef4432f0
-- title:
--   Tri Sqrt: det minor
-- statement:
--   The Tri Sqrt construction uses the det minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrt.lean#L23-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContinuousOnNormDiagOfTriangularSqrt.lean#L23-L59

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

theorem GlobalTheory.TriSqrt.det_minor {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') (d : n → ℝ)
    (S : Matrix n n ℂ) (hs : ∀ j j', S j j' ≠ 0 → t j = t j' ∧ w j ≤ w j')
    (p : n → Prop) [DecidablePred p] (hp : ∀ c a, S c a ≠ 0 → p a → p c) :
    ((Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))).submatrix
      (Subtype.val : {x // p x} → n) Subtype.val).det
      = ((∏ c ∈ Finset.univ.filter p, ‖S c c‖ ^ 2 * d c : ℝ) : ℂ) := by sorry
