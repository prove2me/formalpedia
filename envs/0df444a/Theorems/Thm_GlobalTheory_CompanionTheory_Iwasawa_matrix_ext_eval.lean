-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_matrix_ext_eval
-- name    : GlobalTheory.CompanionTheory.Iwasawa.matrix_ext_eval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:52.140257+00:00
-- url     : https://prove2.me/theorems/0b3af590-ee07-4b1d-83c8-f6e9652816e6
-- title:
--   Iwasawa: matrix ext eval
-- statement:
--   The Iwasawa construction uses the matrix ext eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L62-L66

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

theorem GlobalTheory.CompanionTheory.Iwasawa.matrix_ext_eval {ι : Type} {n : ℕ} {X X' : Matrix (Fin n) (Fin n) (ι → ℂ)}
    (h : ∀ w, evalMat w X = evalMat w X') : X = X' := by sorry
