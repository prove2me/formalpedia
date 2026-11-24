-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_schur
-- name    : GlobalTheory.CompanionTheory.HermDiag.diagble_schur
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:54.199319+00:00
-- url     : https://prove2.me/theorems/9c5abc55-bc44-4e23-8be1-66cc8441ab95
-- title:
--   Herm Diag: diagble schur
-- statement:
--   The Herm Diag construction uses the diagble schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L95-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L95-L164

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
variable {σ : R →+* R} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.CompanionTheory.HermDiag.diagble_schur (hinv : ∀ a, σ (σ a) = a) (ih : ∀ h : Matrix ι ι R, Hm σ h → Diagble σ h)
    {h : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R} (hh : Hm σ h)
    (hu : IsUnit (h (Sum.inl ()) (Sum.inl ()))) : Diagble σ h := by sorry
