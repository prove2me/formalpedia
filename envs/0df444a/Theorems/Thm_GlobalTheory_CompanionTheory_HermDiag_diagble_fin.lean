-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_fin
-- name    : GlobalTheory.CompanionTheory.HermDiag.diagble_fin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:49.077804+00:00
-- url     : https://prove2.me/theorems/c5f6fc7e-e608-41cc-85ff-71eca7dacbbc
-- title:
--   Herm Diag: diagble fin
-- statement:
--   The Herm Diag construction uses the diagble fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L297-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianMatrixDiagonalizable.lean#L297-L310

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

theorem GlobalTheory.CompanionTheory.HermDiag.diagble_fin (hR : IsUnrQuad R σ ϖ q ε) :
    ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), Hm σ h → Diagble σ h := by sorry
