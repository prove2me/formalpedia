-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegCov_red_cT
-- name    : GlobalTheory.CompanionTheory.SiegCov.red_cT
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:35.971843+00:00
-- url     : https://prove2.me/theorems/0ba7b958-e697-4816-b43f-48488f4a597c
-- title:
--   Sieg Cov: red c T
-- statement:
--   The Sieg Cov construction uses the red c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L75-L78

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegCov
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegCov.red_cT (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) : red ϖ k (cT σ x) = cT (barσ σ ϖ hf k) (red ϖ k x) := by sorry
