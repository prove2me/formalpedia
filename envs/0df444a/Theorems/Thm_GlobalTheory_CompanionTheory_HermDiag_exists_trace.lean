-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_exists_trace
-- name    : GlobalTheory.CompanionTheory.HermDiag.exists_trace
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:48:41.691046+00:00
-- url     : https://prove2.me/theorems/75742d29-c274-4430-bebb-fadd40e92bec
-- title:
--   Herm Diag: exists trace
-- statement:
--   The Herm Diag construction uses the exists trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L171-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L171-L185

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
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}

theorem GlobalTheory.CompanionTheory.HermDiag.exists_trace (hR : IsUnrQuad R σ ϖ q ε) {y : R} (hy : y ∉ lev ϖ 1) :
    ∃ s, s * y + σ (s * y) ∉ lev ϖ 1 := by sorry
