-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussProd_chi_sum
-- name    : GlobalTheory.CompanionTheory.GaussProd.chi_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:35.103946+00:00
-- url     : https://prove2.me/theorems/ba99276d-a446-4789-afde-67ae376bec6e
-- title:
--   Gauss Prod: chi sum
-- statement:
--   The Gauss Prod construction uses the chi sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumDiagonalFactor.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumDiagonalFactor.lean#L14-L20

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

theorem GlobalTheory.CompanionTheory.GaussProd.chi_sum {ι Q : Type} [AddCommMonoid Q] (χ : AddChar Q ℂ) (s : Finset ι) (g : ι → Q) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by sorry
