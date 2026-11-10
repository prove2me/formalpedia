-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_lemma_B_1
-- name    : MinimaxATE.Learnability.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:02:17.895431+00:00
-- url     : https://prove2.me/theorems/233f3872-7cd9-45f8-9cbd-484dcffc9061
-- title:
--   Lemma B.1 — product-error identity for the DR score
-- statement:
--   Let $c\in(0,1/2)$ and let $D$ be an observational study with potential outcomes in $[0,1]$ that satisfies unconfoundedness and $c$-overlap (Definition 8), and let $p_D, m_{D,0}, m_{D,1}$ be versions of its propensity score and outcome regressions. Fix (conditionally on the training sample) measurable nuisance estimates $\hat p:\mathcal X\to[c,1-c]$ and $\hat m_0,\hat m_1:\mathcal X\to[0,1]$, and let $\psi_{\hat p,\hat m}$ be the DR score of a fresh observation $(X,T,Y)\sim C_D$. Then
--   $$E_D[\psi_{\hat p,\hat m}]-\tau_D=E_D\Big[(p_D(X)-\hat p(X))\Big(\frac{m_{D,1}(X)-\hat m_1(X)}{\hat p(X)}+\frac{m_{D,0}(X)-\hat m_0(X)}{1-\hat p(X)}\Big)\Big],$$
--   and consequently
--   $$\big|E_D[\psi_{\hat p,\hat m}]-\tau_D\big|\le\frac1c\sum_{t=0}^{1}E_D\big[|p_D(X)-\hat p(X)|\,|m_{D,t}(X)-\hat m_t(X)|\big].$$
--
--   This is the bias bound that makes the doubly robust estimator robust: the bias is a product of the two nuisance errors. It is the first step of the analysis of the per-part estimator (Lemma 4.4).
--
--   **Formalization Note.** "Conditional on $D_T$" is encoded by fixing $\hat p,\hat m_0,\hat m_1$ as deterministic measurable functions. Expectations are Bochner integrals over the full-data law; every integrand is bounded and almost everywhere measurable (the realizing functions agree a.s. with conditional expectations), so no integral is a junk value.
--
--   Differences from the source:
--   - generalization: D ∈ D(P, M, c) → any study with outcomes in [0, 1] satisfying Definition 8 with c-overlap, and any versions p, m₀, m₁ of its nuisances; reason: the lemma never uses the classes; a study of D(P, M, c) with its realizing class members is an instance.
--   - encoding: conditional on the training sample D_T → p̂, m̂₀, m̂₁ fixed measurable functions; reason: conditioning on D_T fixes them; same statement for each training sample.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 53 (PDF 55), Lemma B.1

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_DRScore

open MeasureTheory

namespace MinimaxATE.Learnability

theorem lemma_B_1 {X : Type*} [MeasurableSpace X] (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1 / 2)
    (D : Study X) (hY : OutcomesInUnit D) (hU : Unconfounded D) (hO : Overlap c D)
    (p m₀ m₁ : X → ℝ) (hR : Realizes D p m₀ m₁)
    (pH m₀H m₁H : X → ℝ) (hpH : Measurable pH) (hm₀H : Measurable m₀H) (hm₁H : Measurable m₁H)
    (hpHr : ∀ x, pH x ∈ Set.Icc c (1 - c)) (hm₀Hr : ∀ x, m₀H x ∈ Set.Icc (0 : ℝ) 1)
    (hm₁Hr : ∀ x, m₁H x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, drScore pH m₀H m₁H (observe ω) ∂(D : Measure (FullData X))) - ate D =
        ∫ ω, (p ω.1 - pH ω.1) *
            ((m₁ ω.1 - m₁H ω.1) / pH ω.1 + (m₀ ω.1 - m₀H ω.1) / (1 - pH ω.1))
          ∂(D : Measure (FullData X)) ∧
      |(∫ ω, drScore pH m₀H m₁H (observe ω) ∂(D : Measure (FullData X))) - ate D| ≤
        (1 / c) * ((∫ ω, |p ω.1 - pH ω.1| * |m₀ ω.1 - m₀H ω.1| ∂(D : Measure (FullData X))) +
          ∫ ω, |p ω.1 - pH ω.1| * |m₁ ω.1 - m₁H ω.1| ∂(D : Measure (FullData X))) := by sorry

end MinimaxATE.Learnability
