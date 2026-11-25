-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_chart_image_and_trans
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:23:27.907805+00:00
-- url     : https://prove2.me/theorems/0a308648-6de6-5639-b310-2f936487caca
-- title:
--   Snc Res: chart image and trans
-- statement:
--   The Snc Res construction uses the chart image and trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionTransitionPolynomial.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionTransitionPolynomial.lean#L76-L84

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_image_and_trans (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    (∀ p : (k : K) → ι k, coord P p '' src P p = {t | ∀ h ∈ ideal P p, eval t h = 0}) ∧
    ∀ p p' : (k : K) → ι k, ∀ x ∈ src P p ∩ src P p',
      ∃ (q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)
        (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ),
        eval (coord P p x) q ≠ 0 ∧ ∀ y ∈ src P p ∩ src P p', eval (coord P p y) q ≠ 0 →
          ∀ l, coord P p' y l * eval (coord P p y) q = eval (coord P p y) (F l) := by sorry
