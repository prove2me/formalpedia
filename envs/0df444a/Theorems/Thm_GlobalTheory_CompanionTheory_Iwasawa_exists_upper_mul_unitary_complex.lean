-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_exists_upper_mul_unitary_complex
-- name    : GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary_complex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:37.131826+00:00
-- url     : https://prove2.me/theorems/57973a3f-daf7-4706-8bf6-14b0f7866806
-- title:
--   Iwasawa: exists upper mul unitary complex
-- statement:
--   The Iwasawa construction uses the exists upper mul unitary complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L9-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L9-L47

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwasawa

theorem GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary_complex {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y) :
    ∃ B R K : Matrix (Fin n) (Fin n) ℂ, B.IsUpperTriangular ∧ B * R = 1 ∧ R * B = 1 ∧
      K * Kᴴ = 1 ∧ Kᴴ * K = 1 ∧ Y = B * K := by sorry
