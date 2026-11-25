-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Ktan_tangent_eq_zero
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.tangent_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:23.650414+00:00
-- url     : https://prove2.me/theorems/5447161f-e1fd-554d-97ef-8ce63c9878fc
-- title:
--   Ktan: tangent eq zero
-- statement:
--   The Ktan construction uses the tangent eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean#L57-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean#L57-L167

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
open TrivSqZeroExt

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.tangent_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) [Fintype σ] (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (e : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ) (t v : σ → ℂ) (c : Fin e → ℂ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → eval t (map (algebraMap ℚ ℂ) F) ≠ 0 → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) G)) = 0) → (∀ i, eval t (map (algebraMap ℚ ℂ) (Z i)) = c i * eval t (map (algebraMap ℚ ℂ) F) ^ N i) → (∀ i, ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)) = 0) → v = 0 := by sorry
