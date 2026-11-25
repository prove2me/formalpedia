-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_exists_upper
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.exists_upper
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:23.977869+00:00
-- url     : https://prove2.me/theorems/b9d53642-14d4-57a3-9c35-67f3c7cc6f90
-- title:
--   Is Block Diag: exists upper
-- statement:
--   The Is Block Diag construction uses the exists upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L150-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L150-L175

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]

theorem GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.exists_upper {G : Matrix (Fin N) (Fin N) R} (hG : IsBlockDiag j G)
    (hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det) :
    ∃ B, IsBlockDiag j B ∧ B.BlockTriangular id ∧ IsLowerUni (G * B) := by sorry
