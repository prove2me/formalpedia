-- Prove2me | Theorems.Thm_GlobalTheory_conj_apply_conj_of_entire
-- name    : GlobalTheory.conj_apply_conj_of_entire
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:09.954799+00:00
-- url     : https://prove2.me/theorems/014b6876-9992-470a-9b30-0113a383f8f0
-- title:
--   Global Theory: conj apply conj of entire
-- statement:
--   The Global Theory construction uses the conj apply conj of entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZetaEulerProductNeZeroOneAddMulI.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ZetaEulerProductNeZeroOneAddMulI.lean#L11-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZetaEulerProductNeZeroOneAddMulI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.conj_apply_conj_of_entire (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (h : ∀ s : ℂ, 1 < s.re → starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s) (s : ℂ) :
    starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by sorry
