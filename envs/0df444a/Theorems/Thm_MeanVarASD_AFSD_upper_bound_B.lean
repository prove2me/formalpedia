-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_upper_bound_B
-- name    : MeanVarASD.AFSD.upper_bound_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:37.654033+00:00
-- url     : https://prove2.me/theorems/15452f60-236d-4a83-908e-807f8ee83446
-- title:
--   Proof of Theorem 7, p. 7 — E u_U(X;δ) ≤ B(γ,δ) = γ(µX − δ) + (1 − γ)½(µX − δ + √(σX² + (µX − δ)²))
-- statement:
--   Let $X$ be a random variable with finite variance, mean $\mu_X$ and standard deviation $\sigma_X$, and let $0\le\gamma\le1$, $\delta\in\mathbb R$. Then $u_U(X;\delta)$ is integrable and
--   $$\mathbb E\,u_U(X;\delta)\le B(\gamma,\delta)=\gamma(\mu_X-\delta)+(1-\gamma)\tfrac12\Big(\mu_X-\delta+\sqrt{\sigma_X^2+(\mu_X-\delta)^2}\Big).$$
--
--   The paper defines $B(\gamma,\delta)$ as the maximum of $\mathbb E\,u_U(X;\delta)$ over all $X$ with mean $\mu_X$ and variance $\sigma_X^2$ and evaluates it with Lemma 4; the inequality is the half of that identity the proof of Theorem 7 uses.
--
--   **Formalization Note** Finite variance is `MemLp X 2 P`; $\mu_X=\int X\,dP$ and $\sigma_X=\sqrt{\operatorname{Var}X}$. Attainment of the maximum (the two-point law of Lemma 4) is not stated.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 7 (PDF 8), proof of Theorem 7, definition and evaluation of B(γ, δ)

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 7, p. 7: for `0 ≤ γ ≤ 1` and a square-integrable `X` with mean `µX` and
standard deviation `σX`, `E u_U(X; δ)` exists and is at most `B(γ, δ)`. -/
theorem upper_bound_B {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (γ δ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Integrable (fun ω => uU γ δ (X ω)) P ∧
      ∫ ω, uU γ δ (X ω) ∂P ≤ Bval γ δ (∫ ω, X ω ∂P) (Real.sqrt (variance X P)) := by sorry

end MeanVarASD.AFSD
