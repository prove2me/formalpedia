-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_lemma_A_1
-- name    : MFGLiquidation.Equilibrium.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:24.724763+00:00
-- url     : https://prove2.me/theorems/72816609-8892-4cd1-95f7-801e72c622b6
-- title:
--   Lemma A.1 — the singular stochastic Riccati BSDE has a unique solution in S²([0,T−]) × L²([0,T−]), with the estimate (A.1)
-- statement:
--   Let $\lambda$ and $\eta$ be $\mathbb F$-progressive, nonnegative and essentially bounded, with $1/\eta$ bounded (i.e. $\eta\ge c>0$ a.e.). Then the BSDE with singular terminal value
--   $$-dA_t=\Big(2\lambda_t-\frac{A_t^2}{2\eta_t}\Big)dt-Z^A_t\,d\widetilde W_t,\qquad A_T=\infty,$$
--   has a solution $(A,Z^A)\in S^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R)\times L^2_{\mathbb F}([0,T-]\times\Omega;\mathbb R^m)$, unique in this class ($A$ agrees a.s. at each $t<T$, $Z^A$ agrees $dt\otimes d\mathbb P$-a.e. on each $[0,\tau]$, $\tau<T$). Moreover every solution satisfies, a.s. for every $t<T$,
--   $$\frac{1}{\mathbb E\Big[\int_t^T\frac{1}{2\eta_s}ds\ \Big|\ \mathcal F_t\Big]}\le A_t\le\frac{1}{(T-t)^2}\,\mathbb E\Big[\int_t^T\big(2\eta_s+2(T-s)^2\lambda_s\big)ds\ \Big|\ \mathcal F_t\Big].$$
--   The process $A$ is the decoupling coefficient $Y=AX+B$ of the equilibrium FBSDE in the absence of interaction; the bounds (A.1) give its blow-up rate $A_t\asymp(T-t)^{-1}$ at the liquidation time.
--
--   **Formalization Note** The paper (§A) assumes "$\lambda$, $\eta$ and $1/\eta$ bounded"; these are the hypotheses, together with $\mathbb F$-progressivity and the nonnegativity of the cost coefficients ($L^\infty_{\mathbb F}([0,T]\times\Omega;[0,\infty))$, Assumption 2.3 i)), and nothing else of Assumption 2.3 is assumed: neither (2.4), nor $1/\lambda$ bounded, nor any condition on $\kappa$. The paper writes $dW_t$ for the $m$-dimensional $\widetilde W$ (its $Z^A$ is $\mathbb R^m$-valued). $A_T=\infty$ is $A_t\to+\infty$ as $t\uparrow T$ a.s. The conditional expectations are of integrable variables (bounded, since $\eta\ge c>0$ and $\eta,\lambda$ are bounded), and the denominator is a.s. positive, so no junk value enters.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 31, Lemma A.1, (A.1)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem lemma_A_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (D : Data Ω k) (hD : D.Standing P)
    (hprog_lam : IsStronglyProgressive (filtF hD) D.lam)
    (hprog_η : IsStronglyProgressive (filtF hD) D.η)
    (hbdd_lam : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P),
      0 ≤ D.lam p.1.toNNReal p.2 ∧ D.lam p.1.toNNReal p.2 ≤ c)
    (hbdd_η : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.η p.1.toNNReal p.2 ∧ D.η p.1.toNNReal p.2 ≤ c)
    (hlow_η : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.η p.1.toNNReal p.2) :
    (∃ (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ), IsSingularRiccati hD A ZA) ∧
    (∀ (A A' : ℝ≥0 → Ω → ℝ) (ZA ZA' : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      IsSingularRiccati hD A ZA → IsSingularRiccati hD A' ZA' →
      (∀ t < D.T, A' t =ᵐ[P] A t) ∧ ∀ τ < D.T, ∀ j, AEEqT τ P (ZA' j) (ZA j)) ∧
    (∀ (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      IsSingularRiccati hD A ZA → ∀ t < D.T, ∀ᵐ ω ∂P,
        1 / (P[fun ω' => ∫ s in Set.Icc (t : ℝ) D.T, 1 / (2 * D.η s.toNNReal ω') |
            filtF hD t] ω) ≤ A t ω ∧
        A t ω ≤ 1 / ((D.T : ℝ) - t) ^ 2 *
          (P[fun ω' => ∫ s in Set.Icc (t : ℝ) D.T,
              (2 * D.η s.toNNReal ω' + 2 * ((D.T : ℝ) - s) ^ 2 * D.lam s.toNNReal ω') |
            filtF hD t] ω)) := by sorry

end MFGLiquidation.Equilibrium
