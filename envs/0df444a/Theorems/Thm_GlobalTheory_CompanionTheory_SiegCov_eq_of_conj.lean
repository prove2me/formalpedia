-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegCov_eq_of_conj
-- name    : GlobalTheory.CompanionTheory.SiegCov.eq_of_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:45.709632+00:00
-- url     : https://prove2.me/theorems/674f42e0-05be-433f-ab66-a012c581f370
-- title:
--   Sieg Cov: eq of conj
-- statement:
--   The Sieg Cov construction uses the eq of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MatrixGaussSumCongrInvariance.lean#L46-L52

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
variable {A : Type} [CommRing A]

theorem GlobalTheory.CompanionTheory.SiegCov.eq_of_conj (τ : A →+* A) {n : ℕ} {h D g g' : Matrix (Fin n) (Fin n) A}
    (hg : g * g' = 1) (hD : cT τ g * h * g = D) : h = cT τ g' * D * g' := by sorry
