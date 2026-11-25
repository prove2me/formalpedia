-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_FlagModel_lam_ne_zero
-- name    : GlobalTheory.CompanionTheory.Ar.PB.FlagModel.lam_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:24.373198+00:00
-- url     : https://prove2.me/theorems/a9beb141-4379-54c5-a1f0-806db6aa0a17
-- title:
--   Flag Model: lam ne zero
-- statement:
--   The Flag Model construction uses the lam ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L488-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L488-L494

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [instance] FlagModel.fieldΩ FlagModel.charΩ FlagModel.alg
open GlobalTheory.CompanionTheory.Ar.PB.FlagModel
variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)

theorem GlobalTheory.CompanionTheory.Ar.PB.FlagModel.lam_ne_zero (p : Ψ × Fin N) (hp : M.blk p = none) : M.lam p ≠ 0 := by sorry
