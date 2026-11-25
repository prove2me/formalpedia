-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_exists_mul_pow_eq_aeval_of_mem_adjoin_inv
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.exists_mul_pow_eq_aeval_of_mem_adjoin_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:39:58.722796+00:00
-- url     : https://prove2.me/theorems/8ffb1526-536f-51d3-9733-6553f16a12c3
-- title:
--   Cmp: exists mul pow eq aeval of mem adjoin inv
-- statement:
--   The Cmp construction uses the exists mul pow eq aeval of mem adjoin inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsMulPowEqAevalOfMemAdjoinInv.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ExistsMulPowEqAevalOfMemAdjoinInv.lean#L9-L36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsMulPowEqAevalOfMemAdjoinInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.exists_mul_pow_eq_aeval_of_mem_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω), aeval τ F ≠ 0 →
      S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      ∀ s : S, ∃ (N : ℕ) (G : MvPolynomial σ ℚ), (s : Ω) * aeval τ F ^ N = aeval τ G := by sorry
