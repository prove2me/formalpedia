-- Prove2me | Theorems.Thm_LG2021_theorem_2
-- name    : LG2021.theorem_2
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:35:38.392596+00:00
-- url     : https://prove2.me/theorems/35643b54-e2dc-41cd-b3c6-1757235aaec9
-- title:
--   Theorem 2 — explicit stochastic convex-bandit regret
-- statement:
--   There exists one universal constant $C\ge0$ such that for every integer dimension $d\ge1$, horizon $n\ge2$, and known compact convex set $K\subseteq\mathbb R^d$ containing a closed Euclidean unit ball (with arbitrary center), there exists a measurable randomized bandit policy supported on $K$ satisfying
--   $$\mathbb E\!\left[\sum_{t=1}^{n}\left(L(X_t)-\inf_{x\in K}L(x)\right)\right]
--   \le C\,d^{9/2}\sqrt n\,\log^{3/2}(n\operatorname{diam}K)\max\left\{1,\frac{\sqrt{\log(n\operatorname{diam}K)}}d\right\}.$$
--   The probability space and policy are chosen before the unknown loss and observation kernel. The guarantee holds for every convex loss $L:K\to[0,1]$ that is one-Lipschitz on $K$. The compact body contains a unit ball, so its diameter is at least two. Lipschitz continuity ensures that the displayed infimum is attained; the formal statement uses the infimum for compatibility with the bounded-convex extension.
--
--   At every legal query, the adaptive observation kernel is conditionally centered at the loss and satisfies $\mathbb E[\exp((Y-L(x))^2)\mid\text{history},x]\le2$. Apart from this measurable conditional constraint, the noise may depend on the full prior legal query and observation history.
--
--   This formalizes the statistical regret guarantee of Theorem 2 of Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134. The full dimension and logarithmic dependence is explicit, with a single universal constant. Modifications to allow formalization include the centered Gaussian score $XX^\top-I$, direct density comparisons in the separation argument, concentration for adaptive observation kernels, charges for both observations in each iteration, legal radial query guards, measurable ellipsoid choices from countable rational cut histories, an infimal-convolution Lipschitz extension, and sharp bookkeeping for the sample and simplex-volume stage bounds. The theorem asserts the statistical existence guarantee; computational efficiency, oracle complexity, and bit complexity are not asserted.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Theorem 2, printed p. 1, with Sections 4–7 and Appendices B–E. Statistical regret bound with explicit dimension, horizon, and diameter dependence.

import Mathlib
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_RegretRate
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric

theorem LG2021.theorem_2 : ∃ C : ℝ, 0 ≤ C ∧
∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → LipschitzOnWith 1 L K →
            (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n) := by sorry
