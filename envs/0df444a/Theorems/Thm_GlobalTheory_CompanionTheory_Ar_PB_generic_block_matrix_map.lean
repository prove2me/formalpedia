-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_generic_block_matrix_map
-- name    : GlobalTheory.CompanionTheory.Ar.PB.generic_block_matrix_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:23.237958+00:00
-- url     : https://prove2.me/theorems/a2c69041-897e-4269-906b-daa0a67977ee
-- title:
--   PB: generic block matrix map
-- statement:
--   The PB construction uses the generic block matrix map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L197-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L197-L204

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

theorem GlobalTheory.CompanionTheory.Ar.PB.generic_block_matrix_map (f : MvPolynomial (inertBlockIndex Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ)) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2) (τ : Ψ) :
    (genericBlockMatrix R N j τ).map f = H τ := by sorry
