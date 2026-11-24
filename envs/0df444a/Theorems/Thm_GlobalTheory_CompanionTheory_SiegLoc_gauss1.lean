-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_gauss1
-- name    : GlobalTheory.CompanionTheory.SiegLoc.gauss1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:38.489091+00:00
-- url     : https://prove2.me/theorems/ddbbe4a8-14ce-4559-9434-9e011e4fc94a
-- title:
--   Sieg Loc: gauss1
-- statement:
--   The Sieg Loc construction uses the gauss1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeriesEqDens.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeriesEqDens.lean#L20-L32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizableStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShiftStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonalityStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeriesEqDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc

theorem GlobalTheory.CompanionTheory.SiegLoc.gauss1 {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) (a : R) (ha : σ a = a) (ha' : a ∉ lev ϖ 1) :
    (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by sorry
