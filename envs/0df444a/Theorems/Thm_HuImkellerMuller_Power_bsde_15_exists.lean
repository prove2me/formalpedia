-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_bsde_15_exists
-- name    : HuImkellerMuller.Power.bsde_15_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:31.252643+00:00
-- url     : https://prove2.me/theorems/e641babd-d6f2-45bc-9927-fbc32600c296
-- title:
--   Proof of Theorem 14, p. 18 — the BSDE (15) has a solution (Y, Z) ∈ ℋ^∞(ℝ) × ℋ²(ℝ^m)
-- statement:
--   Assume the setting of §1: an $m$-dimensional Brownian motion $W$ with its augmented filtration, a market $(b,\sigma)$ satisfying the standing hypotheses, a closed nonempty $\tilde C\subseteq\mathbb R^{1\times d}$, and $\gamma\in(0,1)$. Then the BSDE
--   $$
--   Y_t=0-\int_t^T Z_s\,dW_s-\int_t^T f(s,Z_s)\,ds,\qquad t\in[0,T],
--   $$
--   with the power-utility driver $f$ of (15), has a solution $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$.
--
--   The paper obtains it from Kobylanski's existence theorem for BSDEs with quadratic growth (Theorem 2.3 of [11]).
--
--   **Formalization Note** The stochastic integral is given by an Itô-integral operator `I`. $\tilde C\neq\emptyset$ is added (it is needed for (4)).
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 14, p. 18, first paragraph

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Proof of Theorem 14, p. 18: the BSDE (15) has a solution `(Y, Z) ∈ ℋ^∞(ℝ) × ℋ²(ℝᵐ)`. -/
theorem bsde_15_exists
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)),
      IsSolution15 P 𝓕 T I b σ Ct γ Y Z := by sorry

end HuImkellerMuller.Power
