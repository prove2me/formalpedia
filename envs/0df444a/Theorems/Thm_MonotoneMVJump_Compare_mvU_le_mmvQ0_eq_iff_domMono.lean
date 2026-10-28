-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_mvU_le_mmvQ0_eq_iff_domMono
-- name    : MonotoneMVJump.Compare.mvU_le_mmvQ0_eq_iff_domMono
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:51:19.430647+00:00
-- url     : https://prove2.me/theorems/536561e3-67d0-4875-83bf-b1b19e7d9856
-- title:
--   MV utility lies below MMV utility over $\mathcal Q_0$, with equality iff $X\in\mathcal G_\theta$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be the probability space of the market, let $\theta>0$, and let $X\in L^2(\mathbb P)$ be a square-integrable terminal wealth. Write
--   1. $U_\theta(X)=\mathbb E[X]-\frac{\theta}{2}\mathrm{Var}(X)$ for the mean-variance (MV) utility;
--   2. $V^0_\theta(X)=\inf_{\mathbb Q\in\mathcal Q_0}\Big\{\mathbb E^{\mathbb Q}[X]+\frac{1}{2\theta}\Big(\mathbb E^{\mathbb P}\Big[\big(\tfrac{d\mathbb Q}{d\mathbb P}\big)^2\Big]-1\Big)\Big\}$ for the monotone mean-variance (MMV) utility, where $\mathcal Q_0$ is the set of probability measures $\mathbb Q\ll\mathbb P$ with $\mathbb E^{\mathbb P}[(d\mathbb Q/d\mathbb P)^2]<\infty$;
--   3. $\mathcal G_\theta=\{f\in L^2(\mathbb P): f-\mathbb E^{\mathbb P}[f]\le 1/\theta\ \ \mathbb P\text{-a.s.}\}$ for the domain of monotonicity of MV preferences.
--
--   Then
--   $$U_\theta(X)\le V^0_\theta(X),\qquad\text{and}\qquad U_\theta(X)=V^0_\theta(X)\iff X\in\mathcal G_\theta .$$
--
--   This is the property of MMV preferences (Maccheroni, Marinacci, Rustichini and Taboga, 2009) that the proof of Theorem 9 uses twice: MV utility never exceeds MMV utility, and it falls strictly below it exactly when the wealth leaves the domain of monotonicity (which, by Lemma 4, happens for the optimal MV wealth exactly when Assumption 1 fails).
--
--   **Formalization Note** $V^0_\theta$ is `Market.mmvQ0`, an infimum in the extended reals; the inequality and the equality are between extended reals. $\mathbb P$ is assumed to be a probability measure.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 28, proof of Theorem 9 ("for any admissible π, V_MV(X^π_T) ≤ V^0_MMV(X^π_T) ≤ V_MMV(X^π_T)" and the strict inequality (43)); Maccheroni, Marinacci, Rustichini & Taboga, Portfolio selection with monotone mean-variance preferences, Math. Finance 19 (2009), domain of monotonicity G_θ

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Proof of Theorem 9 (p. 28), via Maccheroni et al. (2009): for `X ∈ L²(ℙ)` and `θ > 0`,
`U_θ(X) ≤ V⁰_θ(X)` (MV lies below MMV over `𝒬₀`), with equality if and only if `X` lies in the
domain of monotonicity `𝒢_θ = {f ∈ L²(ℙ) : f − E[f] ≤ 1/θ ℙ-a.s.}`. -/
theorem mvU_le_mmvQ0_eq_iff_domMono {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (hP : IsProbabilityMeasure M.P) (θ : ℝ) (hθ : 0 < θ) (X : Ω → ℝ) (hX : MemLp X 2 M.P) :
    ((M.mvU θ X : ℝ) : EReal) ≤ M.mmvQ0 θ X ∧
      (((M.mvU θ X : ℝ) : EReal) = M.mmvQ0 θ X ↔ InDomMono M.P θ X) := by sorry

end MonotoneMVJump.Compare
