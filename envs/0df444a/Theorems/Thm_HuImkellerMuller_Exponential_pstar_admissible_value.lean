-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_pstar_admissible_value
-- name    : HuImkellerMuller.Exponential.pstar_admissible_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:49.632695+00:00
-- url     : https://prove2.me/theorems/7a5b243b-1622-411c-80f6-859254789e83
-- title:
--   p. 10 — a predictable selection p* ∈ Π_{C_t}(Z_t + θ_t/α) is admissible and E[−exp(−α(X^{p*}_T − F))] = −exp(−α(x − Y₀))
-- statement:
--   In the setting of Theorem 7, let $(Y,Z)$ be a solution of the BSDE (7) and $p^*$ a predictable process with $p^*_t\in\Pi_{C_t}\big(Z_t+\frac1\alpha\theta_t\big)$ for $\lambda\otimes P$-a.e. $(t,\omega)$. Then for every initial capital $x\in\mathbb R$:
--
--   1. $p^*\in\mathcal A$;
--   2. $R^{(p^*)}_t=-\exp(-\alpha(X^{(p^*)}_t-Y_t))$, $t\in[0,T]$, is a martingale: $E[R^{(p^*)}_t\mathbf 1_A]=E[R^{(p^*)}_s\mathbf 1_A]$ for $0\le s\le t\le T$ and $A\in\mathcal F_s$;
--   3. its expected utility is
--   $$E\Big[-\exp\Big(-\alpha\Big(x+\int_0^T p^*_s\,(dW_s+\theta_s\,ds)-F\Big)\Big)\Big]=-\exp\big(-\alpha(x-Y_0)\big).$$
--
--   This is the "attainment" half of the verification argument for Theorem 7.
--
--   **Formalization Note** "$p^*$ constructed in Lemma 11" is read as any predictable selection. $\mathcal F_0$ is $P$-trivial, so $Y_0$ is a.s. constant and the identity is stated for $P$-a.e. $\omega$. The expectations are lower integrals of the nonnegative $\exp(-\alpha(\cdot))$ (the martingale identity is stated for $-R^{(p^*)}$), and the expected utility is minus a lower integral, an extended real. $\tilde C\ne\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 7, p. 10

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- p. 10: a predictable selection p*_t ∈ Π_{C_t}(Z_t + θ_t/α) is admissible,
`R^(p*)_t = −exp(−α(X^(p*)_t − Y_t))` is a martingale (`E[R_t 1_A] = E[R_s 1_A]` for `s ≤ t ≤ T`,
`A ∈ 𝓕_s`, as lower integrals of `exp(−α(X^(p*) − Y))`), and its expected utility is
−exp(−α(x − Y₀)). -/
theorem pstar_admissible_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) (hT : 0 < T)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (hW : EthierKurtz.IsStandardBrownian P W)
    (𝓕 : Filtration ℝ≥0 mΩ)
    (h𝓕 : CvitanicKaratzas92.Optimality.IsAugmentedBrownianFiltration P W 𝓕)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (hI : CvitanicKaratzas92.Optimality.IsItoIntegralOperator P 𝓕 T W I)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (hmkt : MarketHyp P 𝓕 T b σ)
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    (α : ℝ) (hα : 0 < α)
    (F : Ω → ℝ) (hFmeas : Measurable[𝓕 T] F) (hFbdd : ∃ c : ℝ, ∀ᵐ ω ∂P, |F ω| ≤ c)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m))
    (hYZ : IsSolution7 P 𝓕 T I b σ Ct α F Y Z)
    (pstar : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (hpred : IsPredictable 𝓕 pstar)
    (hsel : ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
      pstar q.1.toNNReal q.2 ∈ proj (Cset Ct σ q.1.toNNReal q.2)
        (Z q.1.toNNReal q.2 + (1 / α) • theta b σ q.1.toNNReal q.2))
    (x : ℝ) :
    Admissible P 𝓕 T I b σ Ct α x pstar ∧
      (∀ s t : ℝ≥0, s ≤ t → t ≤ T → ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
        ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-α * (wealth I b σ x pstar s ω - Y s ω))) ∂P =
          ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-α * (wealth I b σ x pstar t ω - Y t ω))) ∂P) ∧
      ∀ᵐ ω ∂P, expectedUtility P T I b σ α F x pstar =
        ((-Real.exp (-α * (x - Y 0 ω)) : ℝ) : EReal) := by sorry

end HuImkellerMuller.Exponential
