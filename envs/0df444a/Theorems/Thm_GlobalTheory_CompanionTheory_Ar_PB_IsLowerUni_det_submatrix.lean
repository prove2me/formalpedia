-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsLowerUni_det_submatrix
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsLowerUni.det_submatrix
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:53.983868+00:00
-- url     : https://prove2.me/theorems/21e969fd-db07-51bf-8329-c32d67e9ebc1
-- title:
--   Is Lower Uni: det submatrix
-- statement:
--   The Is Lower Uni construction uses the det submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L119-L122

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

theorem GlobalTheory.CompanionTheory.Ar.PB.IsLowerUni.det_submatrix {L : Matrix (Fin N) (Fin N) R} (h : IsLowerUni L) (P : Fin N → Prop)
    [DecidablePred P] : (L.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = 1 := by sorry
