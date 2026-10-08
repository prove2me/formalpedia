-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_lemma_12
-- name    : HuImkellerMuller.Exponential.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:20.766956+00:00
-- url     : https://prove2.me/theorems/b431d292-c8c3-4e55-81af-2830a2bcab9f
-- title:
--   Lemma 12, p. 14 — ∫Z dW and ∫p* dW are P-BMO martingales
-- statement:
--   In the setting of Theorem 7, let $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$ be a solution of the BSDE (7), and let $p^*$ be a predictable process with
--   $$p^*_t\in\Pi_{C_t}\Big(Z_t+\frac1\alpha\theta_t\Big)\qquad\text{for }\lambda\otimes P\text{-a.e. }(t,\omega).$$
--   Then the processes
--   $$\int_0^\cdot Z_s\,dW_s,\qquad\int_0^\cdot p^*_s\,dW_s$$
--   are $P$-BMO martingales.
--
--   The BMO property gives the uniform integrability of the stochastic exponential that makes $R^{(p^*)}$ a true martingale, hence $p^*$ admissible, and enters the uniqueness argument for (7).
--
--   **Formalization Note** The page takes "$p^*$ given by Lemma 11 for $a=Z+\frac1\alpha\theta$"; Lemma 11 proves existence of a selection and singles out no process, so the statement is for every predictable selection. The BMO property is condition (2): local square integrability plus a uniform bound on $E[\int_\tau^T|\xi_s|^2ds\mid\mathcal F_\tau]$ over stopping times $\tau\le T$. $\tilde C\ne\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, Lemma 12, p. 14

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- Lemma 12, p. 14: for a solution (Y, Z) of (7) and a predictable selection
p*_t ∈ Π_{C_t}(Z_t + θ_t/α), the processes ∫ Z dW and ∫ p* dW are P-BMO martingales. -/
theorem lemma_12
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
        (Z q.1.toNNReal q.2 + (1 / α) • theta b σ q.1.toNNReal q.2)) :
    IsBMO P 𝓕 T Z ∧ IsBMO P 𝓕 T pstar := by sorry

end HuImkellerMuller.Exponential
