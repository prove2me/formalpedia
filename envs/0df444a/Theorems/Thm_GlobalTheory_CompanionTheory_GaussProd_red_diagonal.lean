-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussProd_red_diagonal
-- name    : GlobalTheory.CompanionTheory.GaussProd.red_diagonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:43.74198+00:00
-- url     : https://prove2.me/theorems/361214ee-64ad-4076-a5df-27b2e44e300b
-- title:
--   Gauss Prod: red diagonal
-- statement:
--   The Gauss Prod construction uses the red diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumDiagonalFactor.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumDiagonalFactor.lean#L34-L40

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussProd

theorem GlobalTheory.CompanionTheory.GaussProd.red_diagonal {R : Type} [CommRing R] (ϖ : R) (k n : ℕ) (D : Fin n → R) :
    red ϖ k (Matrix.diagonal D) =
      Matrix.diagonal fun i => Ideal.Quotient.mk (lev ϖ k) (D i) := by sorry
