-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_rhostar_admissible_value
-- name    : HuImkellerMuller.Power.rhostar_admissible_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:20.729408+00:00
-- url     : https://prove2.me/theorems/fb79874c-7f5e-4fb8-b48b-cc02f2f2aee4
-- title:
--   Proof of Theorem 14, p. 18 — ρ* ∈ Ã and E[(X^{ρ*}_T)^γ] = x^γ exp(Y₀)
-- statement:
--   In the setting of Theorem 14, let $(Y,Z)$ solve the BSDE (15), let $\rho^*$ be a predictable process with $\rho^*_t\in\Pi_{C_t(\omega)}\big(\frac1{1-\gamma}(Z_t+\theta_t)\big)$ for $\lambda\otimes P$-a.e. $(t,\omega)$, and let $x>0$. Then $\rho^*\in\tilde{\mathcal A}$ and
--   $$
--   E\Big[\big(X^{(\rho^*)}_T\big)^\gamma\Big]=x^\gamma\exp(Y_0),
--   $$
--   where $X^{(\rho^*)}$ is the wealth process (11) with initial capital $x$.
--
--   This is the martingale half of the verification argument: $\tilde R^{(\rho^*)}$ is a martingale with initial value $x^\gamma\exp(Y_0)$ and terminal value $(X^{(\rho^*)}_T)^\gamma$.
--
--   **Formalization Note** As in the paper's proof, the left side is $E[(X_T)^\gamma]$, which the page calls "the power utility from terminal wealth"; the utility $U_\gamma=\frac1\gamma x^\gamma$ of (12) differs by the factor $\frac1\gamma$, which the goal theorem carries. $Y_0$ is $\mathcal F_0$-measurable and hence a.s. constant; the identity is stated for $P$-a.e. $\omega$. "Constructed with Lemma 11" is read as any predictable selection. The expectation is a lower integral in $[0,\infty]$. $\tilde C\neq\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 14, p. 18, second paragraph

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Proof of Theorem 14, p. 18: a predictable selection `ρ*` of (16) is admissible, and its
expected power `E[(X^{(ρ*)}_T)^γ]` equals `x^γ exp(Y₀)` for every initial capital `x > 0`. -/
theorem rhostar_admissible_value
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
    (ρstar : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (hpred : HuImkellerMuller.Exponential.IsPredictable 𝓕 ρstar)
    (h16 : ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
      ρstar q.1.toNNReal q.2 ∈ HuImkellerMuller.Exponential.proj (HuImkellerMuller.Exponential.Cset Ct σ q.1.toNNReal q.2)
        ((1 / (1 - γ)) • (Z q.1.toNNReal q.2 + HuImkellerMuller.Exponential.theta b σ q.1.toNNReal q.2)))
    (x : ℝ) (hx : 0 < x) :
    Admissible P 𝓕 T σ Ct ρstar ∧
      ∀ᵐ ω ∂P, ∫⁻ ω', ENNReal.ofReal ((wealth I b σ x ρstar T ω') ^ γ) ∂P
        = ENNReal.ofReal (x ^ γ * Real.exp (Y 0 ω)) := by sorry

end HuImkellerMuller.Power
