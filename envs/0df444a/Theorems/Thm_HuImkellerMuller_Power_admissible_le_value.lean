-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_admissible_le_value
-- name    : HuImkellerMuller.Power.admissible_le_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:42.970609+00:00
-- url     : https://prove2.me/theorems/3b73d1cb-4988-4937-bcc2-ef10bf112f94
-- title:
--   Proof of Theorem 14, p. 18 — E[(X^ρ_T)^γ] ≤ x^γ exp(Y₀) for every ρ ∈ Ã
-- statement:
--   In the setting of Theorem 14, let $(Y,Z)$ solve the BSDE (15), let $x>0$ and let $\rho\in\tilde{\mathcal A}$ be admissible. Then
--   $$
--   E\Big[\big(X^{(\rho)}_T\big)^\gamma\Big]\le x^\gamma\exp(Y_0),
--   $$
--   where $X^{(\rho)}$ is the wealth process (11) with initial capital $x$.
--
--   This is the supermartingale half of the verification argument: by (14), $\tilde R^{(\rho)}$ is a nonnegative local supermartingale, hence a supermartingale, with initial value $x^\gamma\exp(Y_0)$ and terminal value $(X^{(\rho)}_T)^\gamma$.
--
--   **Formalization Note** The page writes "$E[U(X^{(\rho,x)}_T)]\le\tilde R^{(x)}_0=x^\gamma\exp(Y_0)$ for all $\rho\in\mathcal A$"; its "utility of the terminal wealth" is $(X_T)^\gamma$, and $\mathcal A$ is a slip for $\tilde{\mathcal A}$ of Definition 13. The statement uses $(X_T)^\gamma$; the goal theorem carries the factor $\frac1\gamma$ of $U_\gamma$. The identity is for $P$-a.e. $\omega$ ($Y_0$ is a.s. constant). The expectation is a lower integral in $[0,\infty]$. $\tilde C\neq\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 14, p. 18, third and fourth paragraphs

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Proof of Theorem 14, p. 18: for every admissible `ρ` and every `x > 0`,
`E[(X^{(ρ)}_T)^γ] ≤ x^γ exp(Y₀)`. -/
theorem admissible_le_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)} (hW : EthierKurtz.IsStandardBrownian P W)
    {𝓕 : Filtration ℝ≥0 mΩ}
    (h𝓕 : CvitanicKaratzas92.Optimality.IsAugmentedBrownianFiltration P W 𝓕)
    {I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ}
    (hI : CvitanicKaratzas92.Optimality.IsItoIntegralOperator P 𝓕 T W I)
    {b : ℝ≥0 → Ω → (Fin d → ℝ)} {σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ}
    (hmkt : MarketHyp P 𝓕 T b σ)
    {Ct : Set (Fin d → ℝ)} (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m))
    (hYZ : IsSolution15 P 𝓕 T I b σ Ct γ Y Z)
    (x : ℝ) (hx : 0 < x)
    (ρ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (hρ : Admissible P 𝓕 T σ Ct ρ) :
    ∀ᵐ ω ∂P, ∫⁻ ω', ENNReal.ofReal ((wealth I b σ x ρ T ω') ^ γ) ∂P
      ≤ ENNReal.ofReal (x ^ γ * Real.exp (Y 0 ω)) := by sorry

end HuImkellerMuller.Power
