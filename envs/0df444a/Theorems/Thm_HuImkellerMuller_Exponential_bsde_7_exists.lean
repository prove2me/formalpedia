-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_bsde_7_exists
-- name    : HuImkellerMuller.Exponential.bsde_7_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:06.470104+00:00
-- url     : https://prove2.me/theorems/ea1aa827-4a3d-4520-976f-22d7291a9a67
-- title:
--   p. 9 — the BSDE (7) has a solution (Y, Z) ∈ ℋ^∞(ℝ) × ℋ²(ℝ^m)
-- statement:
--   Let $W$ be an $m$-dimensional Brownian motion on $(\Omega,\mathcal F,P)$ and $\mathbb F$ the $P$-augmentation of its natural filtration; assume the standing market hypotheses on $b,\sigma$; let $\tilde C\subseteq\mathbb R^{1\times d}$ be closed and nonempty, $\alpha>0$, and let the liability $F$ be $\mathcal F_T$-measurable and bounded. Then the BSDE
--   $$Y_t=F-\int_t^T Z_s\,dW_s-\int_t^T f(s,Z_s)\,ds,\qquad t\in[0,T],\tag{7}$$
--   with $f(t,z)=-\frac\alpha2\operatorname{dist}^2\big(z+\frac1\alpha\theta_t,C_t\big)+z\theta_t+\frac1{2\alpha}|\theta_t|^2$, has at least one solution $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$.
--
--   The paper obtains this from Kobylanski's existence theorem for quadratic BSDEs with bounded terminal value [Theorem 2.3 of Kobylanski (2000)].
--
--   **Formalization Note** The stochastic integral is the Itô-integral operator $I$ of the published module `CvitanicKaratzas92_Optimality_Market`; the filtration is the $P$-augmented Brownian filtration (the page says "completion"). $\tilde C\ne\emptyset$ is added. $F$ is bounded $P$-a.s.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 7, p. 9, sentence "Theorem 2.3 in [11] states …"

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- p. 9: the BSDE (7) has at least one solution in ℋ^∞(ℝ) × ℋ²(ℝ^m) (Kobylanski, Theorem 2.3). -/
theorem bsde_7_exists
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
    (F : Ω → ℝ) (hFmeas : Measurable[𝓕 T] F) (hFbdd : ∃ c : ℝ, ∀ᵐ ω ∂P, |F ω| ≤ c) :
    ∃ Y Z, IsSolution7 P 𝓕 T I b σ Ct α F Y Z := by sorry

end HuImkellerMuller.Exponential
