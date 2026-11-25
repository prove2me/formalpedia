-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_relation_homogenises
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:36.407802+00:00
-- url     : https://prove2.me/theorems/8130fe51-244d-4608-a6ed-18148b2913ab
-- title:
--   Homog: relation homogenises
-- statement:
--   The Homog construction uses the relation homogenises property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean#L102-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean#L102-L205

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ)
    (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
    (hP : IsMultiHomogIdeal P) (hQ : IsMultiHomogIdeal Q) (hQp : Q.IsPrime)
    (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) (hf : IsMultiHomog f a)
    (hs' : s' ∉ SncRes.ideal Q p)
    (hrel : s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p) :
    ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by sorry
