-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_univ_decomp
-- name    : GlobalTheory.CompanionTheory.Ar.PB.exists_univ_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:10.710025+00:00
-- url     : https://prove2.me/theorems/560ff69b-5ff8-5bd9-b3cd-4d9d38847bde
-- title:
--   PB: exists univ decomp
-- statement:
--   The PB construction uses the exists univ decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L242-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/GenericBlockMatrixIsBlockDiag.lean#L242-L283

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

theorem GlobalTheory.CompanionTheory.Ar.PB.exists_univ_decomp (Ω : Type) [Field Ω] (Ψ : Type) (N j : ℕ) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra Ω T) (i : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] T)
      (ψ : T →ₐ[Ω] MvPolynomial (LowIdx Ψ N j) Ω) (B : Ψ → Matrix (Fin N) (Fin N) T), Function.Injective i ∧
      (∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (ev : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] Φ), Function.Injective ev →
        ∃ e : T →ₐ[Ω] Φ, Function.Injective e ∧ ∀ a, e (i a) = ev a) ∧
      ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ) ∧
        ((genericBlockMatrix Ω N j τ).map i.toRingHom * B τ).map ψ.toRingHom = genLow Ω N j τ := by sorry
