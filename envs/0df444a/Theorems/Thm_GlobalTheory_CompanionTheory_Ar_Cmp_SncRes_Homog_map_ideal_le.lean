-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_map_ideal_le
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.map_ideal_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:11.350456+00:00
-- url     : https://prove2.me/theorems/5f4b976c-cfec-4209-b698-bee05ac18b20
-- title:
--   Homog: map ideal le
-- statement:
--   The Homog construction uses the map ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean#L63-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean#L63-L94

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
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.map_ideal_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hS : IsMultiHomogIdeal S)
    (p : (k : K) → ι k) (c : K → L)
    (hc : ∀ k, c k * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X ⟨k, p k⟩) = 1) :
    (ideal S p).map (chartSub fun q => c q.1 * algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) ≤
      S.map (algebraMap (MvPolynomial (Σ k, ι k) ℂ) L) := by sorry
