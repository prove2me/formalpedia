-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_driver_local_lipschitz
-- name    : HuImkellerMuller.Exponential.driver_local_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:52.37713+00:00
-- url     : https://prove2.me/theorems/dadb6f7b-687e-4d2d-801d-d5652cc0e216
-- title:
--   p. 9 — |f(s, z¹) − f(s, z²)| ≤ c₃(1 + |z¹| + |z²|)|z¹ − z²|
-- statement:
--   Assume the standing market hypotheses, let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, $\alpha>0$, and let $f$ be the driver of the BSDE (7). There is a constant $c_3$ such that, for $\lambda\otimes P$-a.e. $(s,\omega)$ and all $z^1,z^2\in\mathbb R^m$,
--   $$|f(s,z^1)-f(s,z^2)|\le c_3\big(1+|z^1|+|z^2|\big)|z^1-z^2| .$$
--
--   This local Lipschitz estimate, a consequence of the Lipschitz property of the distance to a closed set, drives the uniqueness argument for (7).
--
--   **Formalization Note** $c_3$ is uniform in $(s,\omega)$, $z^1$, $z^2$. $\tilde C\ne\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 7, last display, p. 9

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- p. 9: |f(s, z¹) − f(s, z²)| ≤ c₃(1 + |z¹| + |z²|)|z¹ − z²|. -/
theorem driver_local_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (hmkt : MarketHyp P 𝓕 T b σ)
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    (α : ℝ) (hα : 0 < α) :
    ∃ c₃ : ℝ, ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
      ∀ z₁ z₂ : EuclideanSpace ℝ (Fin m),
        |driver b σ Ct α q.1.toNNReal q.2 z₁ - driver b σ Ct α q.1.toNNReal q.2 z₂| ≤
          c₃ * (1 + ‖z₁‖ + ‖z₂‖) * ‖z₁ - z₂‖ := by sorry

end HuImkellerMuller.Exponential
