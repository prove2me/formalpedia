-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_bsde_7_unique
-- name    : HuImkellerMuller.Exponential.bsde_7_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:05.448581+00:00
-- url     : https://prove2.me/theorems/76fac1d9-978d-4739-82fd-ceaa032dfcfe
-- title:
--   pp. 9–10 — two solutions of the BSDE (7) in ℋ^∞(ℝ) × ℋ²(ℝ^m) coincide
-- statement:
--   In the setting of Theorem 7 (Brownian filtration, standing market hypotheses, closed nonempty $\tilde C$, $\alpha>0$, bounded $\mathcal F_T$-measurable $F$), let $(Y^1,Z^1)$ and $(Y^2,Z^2)$ in $\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$ both solve the BSDE (7). Then
--
--   1. $Y^1_t=Y^2_t$ almost surely, for every $t\in[0,T]$;
--   2. $Z^1=Z^2$ for $\lambda\otimes P$-a.e. $(t,\omega)$.
--
--   Uniqueness is what makes $Y_0$ in Theorem 7 well defined.
--
--   **Formalization Note** "$Y^1=Y^2$, $Z^1=Z^2$" is read in the natural equivalence classes: $Y$ up to modifications, $Z$ up to $\lambda\otimes P$-null sets (elements of $\mathcal H^2$ are only defined a.e.). $\tilde C\ne\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 7, pp. 9–10

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- pp. 9–10: two solutions of the BSDE (7) in ℋ^∞(ℝ) × ℋ²(ℝ^m) coincide. -/
theorem bsde_7_unique
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
    (Y₁ : ℝ≥0 → Ω → ℝ) (Z₁ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m))
    (Y₂ : ℝ≥0 → Ω → ℝ) (Z₂ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m))
    (h₁ : IsSolution7 P 𝓕 T I b σ Ct α F Y₁ Z₁) (h₂ : IsSolution7 P 𝓕 T I b σ Ct α F Y₂ Z₂) :
    (∀ t ≤ T, Y₁ t =ᵐ[P] Y₂ t) ∧
      ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
        Z₁ q.1.toNNReal q.2 = Z₂ q.1.toNNReal q.2 := by sorry

end HuImkellerMuller.Exponential
