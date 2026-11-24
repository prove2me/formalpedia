-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_evalMat_conjTranspose
-- name    : GlobalTheory.CompanionTheory.Iwasawa.evalMat_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:42.451772+00:00
-- url     : https://prove2.me/theorems/ef33c9be-9724-46e7-9ac2-9a3a231b85bb
-- title:
--   Iwasawa: eval Mat conj Transpose
-- statement:
--   The Iwasawa construction uses the eval Mat conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L56-L60

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

theorem GlobalTheory.CompanionTheory.Iwasawa.evalMat_conjTranspose {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ)) :
    evalMat w Xᴴ = (evalMat w X)ᴴ := by sorry
