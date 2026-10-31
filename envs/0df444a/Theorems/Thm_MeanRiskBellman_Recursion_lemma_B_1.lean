-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_B_1
-- name    : MeanRiskBellman.Recursion.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:29.466605+00:00
-- url     : https://prove2.me/theorems/f2e4fa6b-cfbf-4307-9adb-503964380976
-- title:
--   Lemma B.1, pp. 28–29 — Γ_t is translation invariant, monotone, convex, recursive, local and continuous
-- statement:
--   In the mean-risk market under Assumption 2.2, let $0\le t\le T$ and let $\Gamma_t(X)=(-\mathbb E_t(X_1),\rho_t(X_2))$ be the mean-risk function. For all $X,Y\in L_T(\mathbb R^2)$, $r\in L_t(\mathbb R^2)$ and $\alpha\in L_t$:
--   1. conditional translation invariance: $\Gamma_t(X+r)=\Gamma_t(X)-r$;
--   2. monotonicity: if $X\le Y$ then $\Gamma_t(Y)\le\Gamma_t(X)$;
--   3. conditional convexity: $\Gamma_t(\alpha X+(1-\alpha)Y)\le\alpha\Gamma_t(X)+(1-\alpha)\Gamma_t(Y)$ for $0\le\alpha\le1$;
--   4. recursiveness (for $t\le T-1$): $\Gamma_t(X)=\Gamma_t\big(-\Gamma_{t+1}(X)\big)$;
--   5. locality: $\Gamma_t(I_AX)=I_A\Gamma_t(X)$ for every $A\in\mathcal F_t$;
--   6. continuity: $\lim_{n\to\infty}\Gamma_t(X^n)=\Gamma_t(X)$ whenever $\lim_{n\to\infty}X^n=X$ in $L_T(\mathbb R^2)$.
--
--   Orders are componentwise and pointwise. These properties of $\Gamma_t$ are the ones used in the proofs of Lemma B.2, Lemma 5.2 and Theorem 5.1.
--
--   **Formalization Note.** $L_T(\mathbb R^2)$ is the set of $\mathcal F$-measurable functions $\Omega\to\mathbb R\times\mathbb R$; all identities and inequalities hold pointwise (positive probabilities make a.s. and everywhere coincide for measurable functions). Recursiveness needs $\Gamma_{t+1}$, so it is claimed for $t<T$ only. $I_AX$ is the indicator-truncation `A.indicator X`.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, pp. 28–29, Lemma B.1 (six bullets)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MeanRiskBellman.Recursion

theorem lemma_B_1 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t ≤ M.T) :
    -- conditional translation invariance
    (∀ X r : Ω → ℝ × ℝ, StronglyMeasurable X → StronglyMeasurable[M.ℱ t] r →
      Γ M t (X + r) = Γ M t X - r) ∧
    -- monotonicity
    (∀ X Y : Ω → ℝ × ℝ, StronglyMeasurable X → StronglyMeasurable Y → X ≤ Y →
      Γ M t Y ≤ Γ M t X) ∧
    -- conditional convexity
    (∀ (X Y : Ω → ℝ × ℝ) (α : Ω → ℝ), StronglyMeasurable X → StronglyMeasurable Y →
      StronglyMeasurable[M.ℱ t] α → (∀ ω, 0 ≤ α ω ∧ α ω ≤ 1) →
      Γ M t (fun ω => α ω • X ω + (1 - α ω) • Y ω) ≤
        fun ω => α ω • Γ M t X ω + (1 - α ω) • Γ M t Y ω) ∧
    -- recursiveness
    (t < M.T → ∀ X : Ω → ℝ × ℝ, StronglyMeasurable X →
      Γ M t X = Γ M t (-Γ M (t + 1) X)) ∧
    -- locality
    (∀ (X : Ω → ℝ × ℝ) (A : Set Ω), StronglyMeasurable X → MeasurableSet[M.ℱ t] A →
      Γ M t (A.indicator X) = A.indicator (Γ M t X)) ∧
    -- continuity
    (∀ (Xn : ℕ → Ω → ℝ × ℝ) (X : Ω → ℝ × ℝ), (∀ n, StronglyMeasurable (Xn n)) →
      StronglyMeasurable X → Tendsto Xn atTop (𝓝 X) →
      Tendsto (fun n => Γ M t (Xn n)) atTop (𝓝 (Γ M t X))) := by sorry

end MeanRiskBellman.Recursion
