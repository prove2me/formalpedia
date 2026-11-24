-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_pivot_offdiag
-- name    : GlobalTheory.CompanionTheory.HermDiag.pivot_offdiag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:48:48.148363+00:00
-- url     : https://prove2.me/theorems/242bb8de-6b4d-4e74-adb1-dbab0c51f0c8
-- title:
--   Herm Diag: pivot offdiag
-- statement:
--   The Herm Diag construction uses the pivot offdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L212-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L212-L227

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
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HermDiag.pivot_offdiag (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) {i j : ι}
    (hij : i ≠ j) (hi : h i i ∈ lev ϖ 1) (hj : h j j ∈ lev ϖ 1) (hy : h i j ∉ lev ϖ 1) :
    ∃ p p' : Matrix ι ι R, p * p' = 1 ∧ p' * p = 1 ∧ (ct σ p * h * p) i i ∉ lev ϖ 1 := by sorry
