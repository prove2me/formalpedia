-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerSquare_kernel_rows_columns_square_integrable
-- name    : GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:25.615553+00:00
-- url     : https://prove2.me/theorems/ad8243bc-14ce-42b9-a913-4cfd3910de61
-- title:
--   Ker Square: kernel rows columns square integrable
-- statement:
--   The Ker Square construction uses the kernel rows columns square integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelRowsColumnsSquareIntegrable.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelRowsColumnsSquareIntegrable.lean#L38-L39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelRowsColumnsSquareIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerSquare

theorem GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable : KerBasic → CntBasic → ColSq → KernelL2RowsColumns := by sorry
