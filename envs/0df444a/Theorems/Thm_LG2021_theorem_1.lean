-- Prove2me | Theorems.Thm_LG2021_theorem_1
-- name    : LG2021.theorem_1
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-14T15:42:12.76734+00:00
-- url     : https://prove2.me/theorems/e34484fa-75f4-4514-9cb7-2f3a699822b5
-- title:
--   Theorem 1 — explicit regret for bounded convex bandit losses
-- statement:
--   There exists a universal constant $C\ge0$ such that, for every integer dimension $d\ge1$, horizon $n\ge2$, and known compact convex set $K\subseteq\mathbb R^d$ containing a closed Euclidean unit ball with any center, there is a measurable randomized policy with all queries in $K$ and
--   $$\mathbb E\!\left[\sum_{t=1}^{n}\left(L(X_t)-\inf_{x\in K}L(x)\right)\right]
--   \le C\,d^{9/2}\sqrt n\,\log^{3/2}(n\operatorname{diam}K)
--   \max\left\{1,\frac{\sqrt{\log(n\operatorname{diam}K)}}{d}\right\}.$$
--   The probability seed and policy are chosen before the unknown loss and observation kernel. The guarantee holds for every convex loss $L:K\to[0,1]$, without a boundary continuity assumption. The formal comparator is the infimum of the loss on $K$; it equals the source's minimum comparator whenever a minimum is attained.
--
--   The measurable observation kernel may depend on every previous legal query and observation. At each legal current query $x$, its observation $Y$ has conditional mean $L(x)$ and satisfies $\mathbb E[\exp((Y-L(x))^2)\mid\text{history},x]\le2$, with the indicated moments integrable.
--
--   This is the statistical regret guarantee of Theorem 1 in Lattimore and György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, COLT 2021, PMLR 134. Its proof imports the formalized original dimension-dependent Theorem 2 and follows Appendix F: erode the known body at depth $1/n$, scale the eroded body by $n$, and pull queries and adaptive observations back by the inverse scaling. The scaled loss is one-Lipschitz. The diameter grows by at most $n$, and the cumulative comparator penalty is at most one. The proof makes this reduction explicit for the infimum comparator and for a unit ball with arbitrary center. These adaptations preserve the displayed dimension, horizon, and logarithmic rate with one universal constant. Computational efficiency, oracle complexity, and bit complexity are not asserted. The formalization adaptations in the imported Theorem 2 are documented on that theorem.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory, Proceedings of Machine Learning Research 134:2938–2964, 2021. Theorem 1 (printed p. 1) and Appendix F, Non-Lipschitz case: the proof of Theorem 1 (printed p. 27).

import Mathlib
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_RegretRate

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric LG2021

theorem LG2021.theorem_1 : ∃ C : ℝ, 0 ≤ C ∧
∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n) := by sorry
