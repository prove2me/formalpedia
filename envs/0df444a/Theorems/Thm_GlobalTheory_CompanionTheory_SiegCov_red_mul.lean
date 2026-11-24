-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegCov_red_mul
-- name    : GlobalTheory.CompanionTheory.SiegCov.red_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:02.66422+00:00
-- url     : https://prove2.me/theorems/9b5b7bcc-f057-47ef-98da-7fd4cb940eb7
-- title:
--   Sieg Cov: red mul
-- statement:
--   The Sieg Cov construction uses the red mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L70-L73

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

theorem GlobalTheory.CompanionTheory.SiegCov.red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R)
    (y : Matrix (Fin b) (Fin c) R) : red ϖ k (x * y) = red ϖ k x * red ϖ k y := by sorry
