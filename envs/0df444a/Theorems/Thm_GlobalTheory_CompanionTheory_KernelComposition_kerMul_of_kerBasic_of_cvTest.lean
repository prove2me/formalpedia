-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KernelComposition_kerMul_of_kerBasic_of_cvTest
-- name    : GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:35.710276+00:00
-- url     : https://prove2.me/theorems/101489f5-59b9-4342-9969-2db72239ae3b
-- title:
--   Kernel Composition: ker Mul of ker Basic of cv Test
-- statement:
--   The Kernel Composition construction uses the ker Mul of ker Basic of cv Test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerMulOfKerBasicOfCvTest.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KerMulOfKerBasicOfCvTest.lean#L76-L81

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KerMulOfKerBasicOfCvTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelComposition

theorem GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest : KerBasic → CvTest → KerMul := by sorry
