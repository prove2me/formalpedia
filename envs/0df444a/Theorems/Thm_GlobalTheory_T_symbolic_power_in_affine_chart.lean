-- Prove2me | Theorems.Thm_GlobalTheory_T_symbolic_power_in_affine_chart
-- name    : GlobalTheory.T.symbolic_power_in_affine_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:48:04.992808+00:00
-- url     : https://prove2.me/theorems/622353c0-2495-45f6-b83b-670f254176a1
-- title:
--   T: symbolic power in affine chart
-- statement:
--   The T construction uses the symbolic power in affine chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChartStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChartStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.symbolic_power_in_affine_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s' ∉ SncRes.ideal Q p → s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p → ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by sorry
