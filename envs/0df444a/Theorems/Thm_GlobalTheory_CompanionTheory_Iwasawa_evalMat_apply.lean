-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_evalMat_apply
-- name    : GlobalTheory.CompanionTheory.Iwasawa.evalMat_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:20.919607+00:00
-- url     : https://prove2.me/theorems/7e7dcb45-06e6-4678-aaf4-9781d59580e1
-- title:
--   Iwasawa: eval Mat apply
-- statement:
--   The Iwasawa construction uses the eval Mat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean#L53-L54

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

theorem GlobalTheory.CompanionTheory.Iwasawa.evalMat_apply {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ))
    (i j : Fin n) : evalMat w X i j = X i j w := by sorry
