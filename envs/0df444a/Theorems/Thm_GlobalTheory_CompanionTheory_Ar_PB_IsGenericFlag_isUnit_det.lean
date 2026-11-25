-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsGenericFlag_isUnit_det
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.isUnit_det
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:40.344297+00:00
-- url     : https://prove2.me/theorems/1342115e-9c52-59a9-a0e2-7d56c183cbc3
-- title:
--   Is Generic Flag: is Unit det
-- statement:
--   The Is Generic Flag construction uses the is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L237-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L237-L240

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

theorem GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.isUnit_det {Ω : Type} [CommRing Ω] [Algebra Ω R] {g : Ψ → Matrix (Fin N) (Fin N) R}
    (h : IsGenericFlag Ω j g) (τ : Ψ) : IsUnit (g τ).det := by sorry
