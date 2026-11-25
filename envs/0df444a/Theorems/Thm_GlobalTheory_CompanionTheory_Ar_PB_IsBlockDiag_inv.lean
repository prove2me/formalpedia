-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_inv
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:05.134584+00:00
-- url     : https://prove2.me/theorems/8003541f-0200-51bb-9c61-8f7d715f217b
-- title:
--   Is Block Diag: inv
-- statement:
--   The Is Block Diag construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L98-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L98-L111

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

theorem GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.inv {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (hd : IsUnit A.det) :
    IsBlockDiag j A⁻¹ := by sorry
