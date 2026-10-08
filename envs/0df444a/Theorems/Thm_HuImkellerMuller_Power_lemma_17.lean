-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_lemma_17
-- name    : HuImkellerMuller.Power.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:34.959302+00:00
-- url     : https://prove2.me/theorems/b8381bc6-8363-4bdb-9d99-b7cffb1430e2
-- title:
--   Lemma 17, p. 20 — for a solution (Y, Z) of (15) and ρ* given by (16), ∫Z dW and ∫ρ* dW are BMO martingales
-- statement:
--   In the setting of Theorem 14, let $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$ solve the BSDE (15), and let $\rho^*$ be a predictable process with
--   $$
--   \rho^*_t\in\Pi_{C_t(\omega)}\Big(\frac1{1-\gamma}(Z_t+\theta_t)\Big)\qquad\text{for }\lambda\otimes P\text{-a.e. }(t,\omega).
--   $$
--   Then the processes $\int_0^\cdot Z_s\,dW_s$ and $\int_0^\cdot\rho^*_s\,dW_s$ are $P$-BMO martingales on $[0,T]$.
--
--   The BMO property of $\int\rho^*\,dW$ is what makes the stochastic exponential in $\tilde R^{(\rho^*)}$ a true martingale (Kazamaki's criterion), so that $\rho^*$ attains the value.
--
--   **Formalization Note** "$\rho^*$ given by (16)" is read as any predictable selection of the projection in (16), $\lambda\otimes P$-a.e. (16) has no qualifier on the page; $Z\in\mathcal H^2$ is determined only $\lambda\otimes P$-a.e. BMO is the condition (2) of p. 4, stated with lower integrals over events of $\mathcal F_\tau$. $\tilde C\neq\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, Lemma 17, p. 20

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Lemma 17, p. 20: for a solution `(Y, Z)` of (15) and a predictable `ρ*` with
`ρ*_t ∈ Π_{C_t}((Z_t + θ_t)/(1 − γ))` (16), `λ ⊗ P`-a.e., the processes `∫₀^· Z dW` and
`∫₀^· ρ* dW` are BMO martingales. -/
theorem lemma_17
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
        ((1 / (1 - γ)) • (Z q.1.toNNReal q.2 + HuImkellerMuller.Exponential.theta b σ q.1.toNNReal q.2))) :
    IsBMO P 𝓕 T Z ∧ IsBMO P 𝓕 T ρstar := by sorry

end HuImkellerMuller.Power
