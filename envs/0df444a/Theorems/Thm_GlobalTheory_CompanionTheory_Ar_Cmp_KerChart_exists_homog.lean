-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_KerChart_exists_homog
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.exists_homog
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:49.872378+00:00
-- url     : https://prove2.me/theorems/26bb21c0-4999-44f1-a63f-6ca1138a7834
-- title:
--   Ker Chart: exists homog
-- statement:
--   The Ker Chart construction uses the exists homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MapMemChartIdealOfAevalEqZero.lean#L33-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MapMemChartIdealOfAevalEqZero.lean#L33-L67

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
open MvPolynomial ReciprocityTheory.AnForm.R
variable {σ : Type}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.exists_homog (s : σ → σ) (G₀ : MvPolynomial σ ℤ) :
    ∃ H m : MvPolynomial σ ℤ, ∀ (T : Type) [CommRing T] (f : MvPolynomial σ ℤ →+* T) (w : σ → T),
      (∀ q, IsUnit (f (X (s q)))) → (∀ q, f (X q) = f (X (s q)) * w q) →
      IsUnit (f m) ∧ eval₂Hom (Int.castRingHom T) w G₀ * f m = f H := by sorry
