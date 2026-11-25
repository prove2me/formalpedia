-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsGenericFlag_of_indep
-- name    : GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.of_indep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:28.969825+00:00
-- url     : https://prove2.me/theorems/1aa3ab87-1d79-5302-9619-6174538d753d
-- title:
--   Is Generic Flag: of indep
-- statement:
--   The Is Generic Flag construction uses the of indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L285-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L285-L301

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

theorem GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.of_indep {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {g : Ψ → Matrix (Fin N) (Fin N) Φ}
    (hg : ∀ τ, IsBlockDiag j (g τ))
    (h : AlgebraicIndependent Ω fun q : inertBlockIndex Ψ N j => g q.1.1 q.1.2.1 q.1.2.2) : IsGenericFlag Ω j g := by sorry
