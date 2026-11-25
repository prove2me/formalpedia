-- Prove2me | Theorems.Thm_GlobalTheory_EigenvalueNormAtMostOne_norm_eigenvalue_le_one_of_entries
-- name    : GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one_of_entries
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:42.128836+00:00
-- url     : https://prove2.me/theorems/c394d8e4-92e8-4335-91e6-5089dc663a02
-- title:
--   Eigenvalue Norm At Most One: norm eigenvalue le one of entries
-- statement:
--   The Eigenvalue Norm At Most One construction uses the norm eigenvalue le one of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormEigenvalueLeOneOfEntries.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormEigenvalueLeOneOfEntries.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EigenvalueNormAtMostOne

theorem GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one_of_entries {K : Type} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (c : Fin n → K) (μ : K) (hc : c ≠ 0) (h : A.mulVec c = μ • c) : ‖μ‖ ≤ 1 := by sorry
