-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_gauss_full
-- name    : GlobalTheory.CompanionTheory.SiegLoc.gauss_full
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:15:19.934719+00:00
-- url     : https://prove2.me/theorems/0f10d692-27c7-4340-a1da-2880feaceda7
-- title:
--   Sieg Loc: gauss full
-- statement:
--   The Sieg Loc construction uses the gauss full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeriesEqDens.lean#L34-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeriesEqDens.lean#L34-L91

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

theorem GlobalTheory.CompanionTheory.SiegLoc.gauss_full {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Matrix (Fin m) (Fin m) R) (hS : IsUnimod σ S)
    (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by sorry
