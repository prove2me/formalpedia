-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_mul
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:49.962418+00:00
-- url     : https://prove2.me/theorems/a3998856-091c-474c-9c12-92524575412b
-- title:
--   Is Block Diag: mul
-- statement:
--   The Is Block Diag construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L87-L93

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

theorem GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.mul {A B : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (hB : IsBlockDiag j B) :
    IsBlockDiag j (A * B) := by sorry
