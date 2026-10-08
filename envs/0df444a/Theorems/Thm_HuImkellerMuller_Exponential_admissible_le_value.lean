-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_admissible_le_value
-- name    : HuImkellerMuller.Exponential.admissible_le_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:06.590975+00:00
-- url     : https://prove2.me/theorems/e06d1759-e5d1-4893-ae55-9835feeb96b9
-- title:
--   pp. 10–11 and (6) — for every p ∈ 𝒜, E[−exp(−α(X^p_T − F))] ≤ −exp(−α(x − Y₀))
-- statement:
--   In the setting of Theorem 7, let $(Y,Z)$ be a solution of the BSDE (7), $x\in\mathbb R$, and $p\in\mathcal A$ an admissible strategy. Then
--   $R^{(p)}_t=-\exp(-\alpha(X^{(p)}_t-Y_t))$, $t\in[0,T]$, is a supermartingale,
--   $$E[R^{(p)}_t\mathbf 1_A]\le E[R^{(p)}_s\mathbf 1_A]\qquad(0\le s\le t\le T,\ A\in\mathcal F_s),$$
--   and consequently
--   $$E\big[-\exp\big(-\alpha(X^{(p)}_T-F)\big)\big]\le-\exp\big(-\alpha(x-Y_0)\big).$$
--
--   The second display is the first inequality of (6), $E[-\exp(-\alpha(X^p_T-F))]\le R_0(x)$; with the previous milestone it identifies the value function.
--
--   **Formalization Note** The supermartingale inequality is written for $-R^{(p)}=\exp(-\alpha(X^{(p)}-Y))\ge0$ with lower integrals, so its direction is reversed: $E[\exp(-\alpha(X^{(p)}_s-Y_s))\mathbf 1_A]\le E[\exp(-\alpha(X^{(p)}_t-Y_t))\mathbf 1_A]$. $Y_0$ is a.s. constant, so the last inequality is stated for $P$-a.e. $\omega$. The expected utility is minus a lower integral, an extended real. $\tilde C\ne\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 7, pp. 10–11; (6), p. 7

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- pp. 10–11 and (6), p. 7: for every admissible strategy `p`, `R^(p)_t = −exp(−α(X^(p)_t − Y_t))`
is a supermartingale, `E[R^(p)_t 1_A] ≤ E[R^(p)_s 1_A]` for `s ≤ t ≤ T` and `A ∈ 𝓕_s` (written with
the signs flipped, as lower integrals of `exp(−α(X^(p) − Y))`), and so its expected utility is at
most −exp(−α(x − Y₀)). -/
theorem admissible_le_value
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
    (x : ℝ) (p : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m))
    (hp : Admissible P 𝓕 T I b σ Ct α x p) :
    (∀ s t : ℝ≥0, s ≤ t → t ≤ T → ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-α * (wealth I b σ x p s ω - Y s ω))) ∂P ≤
        ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-α * (wealth I b σ x p t ω - Y t ω))) ∂P) ∧
    ∀ᵐ ω ∂P, expectedUtility P T I b σ α F x p ≤
      ((-Real.exp (-α * (x - Y 0 ω)) : ℝ) : EReal) := by sorry

end HuImkellerMuller.Exponential
