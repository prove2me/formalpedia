-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Homog_chartSub_bind
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.chartSub_bind
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:35:46.8362+00:00
-- url     : https://prove2.me/theorems/f3c7d87e-a319-5226-a596-a64237faf787
-- title:
--   Homog: chart Sub bind
-- statement:
--   The Homog construction uses the chart Sub bind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean#L37-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerInAffineChart.lean#L37-L50

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.chartSub_bind {L : Type} [CommRing L] [Algebra ℂ L] (w : (Σ k, ι k) → L)
    (p : (k : K) → ι k) (h1 : ∀ k, w ⟨k, p k⟩ = 1) (f : MvPolynomial (Σ k, ι k) ℂ) :
    chartSub w (bind₁ (lift p) f) = aeval w f := by sorry
