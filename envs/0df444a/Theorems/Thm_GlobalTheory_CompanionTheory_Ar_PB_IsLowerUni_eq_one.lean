-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsLowerUni_eq_one
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsLowerUni.eq_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:31.055422+00:00
-- url     : https://prove2.me/theorems/8608a0c1-ddc7-5224-bbfd-2636031db7d2
-- title:
--   Is Lower Uni: eq one
-- statement:
--   The Is Lower Uni construction uses the eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L128-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L128-L148

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

theorem GlobalTheory.CompanionTheory.Ar.PB.IsLowerUni.eq_one {L U : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (hU : U.BlockTriangular id)
    (h' : IsLowerUni (L * U)) : U = 1 := by sorry
