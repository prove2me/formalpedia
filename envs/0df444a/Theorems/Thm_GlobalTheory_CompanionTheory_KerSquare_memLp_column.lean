-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerSquare_memLp_column
-- name    : GlobalTheory.CompanionTheory.KerSquare.memLp_column
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:36.59496+00:00
-- url     : https://prove2.me/theorems/e3806ff7-1797-42aa-a479-b84fb1bfe2ef
-- title:
--   Ker Square: mem Lp column
-- statement:
--   The Ker Square construction uses the mem Lp column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelRowsColumnsSquareIntegrable.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelRowsColumnsSquareIntegrable.lean#L10-L27

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

theorem GlobalTheory.CompanionTheory.KerSquare.memLp_column (hK : KerBasic) (hC : CntBasic) (hS : ColSq) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (y : X.G) : MemLp (fun x => ker X.Γ φ x y) 2 X.ν := by sorry
