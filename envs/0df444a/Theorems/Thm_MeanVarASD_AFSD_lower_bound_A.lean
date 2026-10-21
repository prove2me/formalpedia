-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_lower_bound_A
-- name    : MeanVarASD.AFSD.lower_bound_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:52.183094+00:00
-- url     : https://prove2.me/theorems/5378c77d-2919-4754-ad50-d460c49ca9da
-- title:
--   Proof of Theorem 7, p. 7 — E u_L(Y;δ) ≥ A(γ,δ) = γ(µY − δ) − (1 − γ)½(δ − µY + √(σY² + (µY − δ)²))
-- statement:
--   Let $Y$ be a random variable with finite variance, mean $\mu_Y$ and standard deviation $\sigma_Y$, and let $0\le\gamma\le1$, $\delta\in\mathbb R$. Then $u_L(Y;\delta)$ is integrable and
--   $$\mathbb E\,u_L(Y;\delta)\ge A(\gamma,\delta)=\gamma(\mu_Y-\delta)-(1-\gamma)\tfrac12\Big(\delta-\mu_Y+\sqrt{\sigma_Y^2+(\mu_Y-\delta)^2}\Big).$$
--
--   The paper defines $A(\gamma,\delta)$ as the minimum of $\mathbb E\,u_L(Y;\delta)$ over all $Y$ with mean $\mu_Y$ and variance $\sigma_Y^2$, which equals $\gamma(\mu_Y-\delta)-(1-\gamma)\max\mathbb E(\delta-Y)_+$; the inequality is the half of that identity the proof of Theorem 7 uses.
--
--   **Formalization Note** Finite variance is `MemLp Y 2 P`; $\mu_Y=\int Y\,dP$ and $\sigma_Y=\sqrt{\operatorname{Var}Y}$. Attainment of the minimum is not stated.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 7 (PDF 8), proof of Theorem 7, definition and evaluation of A(γ, δ)

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 7, p. 7: for `0 ≤ γ ≤ 1` and a square-integrable `Y` with mean `µY` and
standard deviation `σY`, `E u_L(Y; δ)` exists and is at least `A(γ, δ)`. -/
theorem lower_bound_A {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLp Y 2 P) (γ δ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Integrable (fun ω => uL γ δ (Y ω)) P ∧
      Aval γ δ (∫ ω, Y ω ∂P) (Real.sqrt (variance Y P)) ≤ ∫ ω, uL γ δ (Y ω) ∂P := by sorry

end MeanVarASD.AFSD
