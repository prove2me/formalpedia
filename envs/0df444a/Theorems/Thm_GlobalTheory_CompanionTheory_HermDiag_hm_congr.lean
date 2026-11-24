-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_hm_congr
-- name    : GlobalTheory.CompanionTheory.HermDiag.hm_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:48:39.417976+00:00
-- url     : https://prove2.me/theorems/2769ce6e-f805-4b3e-a889-a1d65f37aa89
-- title:
--   Herm Diag: hm congr
-- statement:
--   The Herm Diag construction uses the hm congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L33-L40

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

theorem GlobalTheory.CompanionTheory.HermDiag.hm_congr (hinv : ∀ a, σ (σ a) = a) {h : Matrix ι ι R} (hh : Hm σ h) (p : Matrix ι ι R) :
    Hm σ (ct σ p * h * p) := by sorry
