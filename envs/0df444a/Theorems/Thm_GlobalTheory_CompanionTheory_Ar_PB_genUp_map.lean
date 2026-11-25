-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_genUp_map
-- name    : GlobalTheory.CompanionTheory.Ar.PB.genUp_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:01.108569+00:00
-- url     : https://prove2.me/theorems/4f88786a-4d76-4836-a389-7048d497cf98
-- title:
--   PB: gen Up map
-- statement:
--   The PB construction uses the gen Up map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L219-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L219-L229

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

theorem GlobalTheory.CompanionTheory.Ar.PB.genUp_map (f : MvPolynomial (UpIdx Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ) ∧ (H τ).BlockTriangular id) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2)
    (τ : Ψ) : (genUp R N j τ).map f = H τ := by sorry
