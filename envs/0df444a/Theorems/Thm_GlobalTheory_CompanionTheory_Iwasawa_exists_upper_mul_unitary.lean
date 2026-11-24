-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_exists_upper_mul_unitary
-- name    : GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:39.646254+00:00
-- url     : https://prove2.me/theorems/5423e106-c0a4-475f-b12c-5ec413c1cc9f
-- title:
--   Iwasawa: exists upper mul unitary
-- statement:
--   The Iwasawa construction uses the exists upper mul unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L68-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L68-L96

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

theorem GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by sorry
