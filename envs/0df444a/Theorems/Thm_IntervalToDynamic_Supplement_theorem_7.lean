-- Prove2me | Theorems.Thm_IntervalToDynamic_Supplement_theorem_7
-- name    : IntervalToDynamic.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:40:37.515891+00:00
-- url     : https://prove2.me/theorems/abcd4cae-1fab-4203-b935-b4a1bdb2b096
-- title:
--   Theorem 7 — algorithmic reduction with fixed $k$
-- statement:
--   Fix $d,k\ge1$, a nonempty compact convex domain $\mathcal X\subseteq B(D_{\mathcal X}/2)$, positive loss parameters, and the enlarged ball $\mathcal Y=B(\kappa_kD_{\mathcal X})$. Uniform constants depending only on this fixed data and $k$ have the following property for every horizon and every selected loss regime.
--
--   If a history-based algorithm remains in $\mathcal Y$ and guarantees polynomial interval regret against every $q\in\mathcal P_{k-1}(I;\mathcal Y)$ on every interval at rate $R\sqrt{|I|}$, $Rd(1+\log|I|)$ or $R(1+\log|I|)$, then the fixed-$k$ Algorithm 1 wrapper produces decisions in $\mathcal X$. For every comparator sequence in $\mathcal X^T$ and every $1\le i\le k$, its dynamic regret is bounded, up to that fixed factor, by
--   $$
--   R(1+P_{T,i}^{1/(2i)})\sqrt T,
--   $$
--   $$
--   R\bigl(d+d^{2i/(2i+1)}P_{T,i}^{2/(2i+1)}T^{1/(2i+1)}\bigr),
--   $$
--   or
--   $$
--   R\bigl(1+P_{T,i}^{2/(2i+1)}T^{1/(2i+1)}\bigr)
--   $$
--   in the convex, exp-concave and strongly convex regimes, respectively. Holding for every $i$ is equivalent to the paper's minimum over $1\le i\le k$.
--
--   Differences from the source:
--   - encoding: $\widetilde O_k$ notation → an explicit positive interval-regret multiplier $R$ and positive reduction constants chosen before the horizon, losses, algorithm and comparator; reason: this preserves the permitted fixed-parameter and polylogarithmic dependence without allowing constants to depend on adversarial data
--   - encoding: a bound by $\min_{1\le i\le k}$ → the same bound asserted separately for every $i\in\{1,\ldots,k\}$; reason: these formulations are logically equivalent for a finite nonempty index set
--   - encoding: differentiable losses → losses accompanied by a gradient oracle satisfying `HasGradientWithinAt` on $\mathcal X$; reason: the domain may have empty interior and this is the published base mission's faithful Assumption 1 convention
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 7, pp.11–12 (PDF pp.13–14); proof, pp.33–35 (PDF pp.35–37)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_HigherVariation
import Definitions.Def_IntervalToDynamic_Supplement_FixedKWrapper
import Definitions.Def_IntervalToDynamic_SatisfiesAssumptions
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

open ModernOnlineLearning.Dynamic (dynamicRegret)

namespace IntervalToDynamic.Supplement

/-- Theorem 7 (algorithmic reduction with fixed `k`), Wang--Zhao--Zhou,
*On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, pp.11--12
(PDF pp.13--14).

The constants hidden by `Õ_k` are chosen before the horizon, losses, algorithm, and comparator.
Writing the conclusion for every `1 ≤ i ≤ k` is equivalent to the displayed minimum over `i`.
The algorithm domain and every surrogate coefficient use `D_Y = 2 κ_k D_X`. -/
theorem theorem_7 {d k : ℕ} (hd : 0 < d) (hk : 1 ≤ k)
    (X : Set (EuclideanSpace ℝ (Fin d))) (DX G alpha lam : ℝ)
    (hDX : 0 < DX) (hG : 0 < G) (halpha : 0 < alpha) (hlam : 0 < lam) :
    ∃ Cconv Cexp Cstrong : ℝ,
      0 < Cconv ∧ 0 < Cexp ∧ 0 < Cstrong ∧
      ∀ (T : ℕ), 1 ≤ T →
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
        (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (A : IntervalToDynamic.OnlineAlgorithm (EuclideanSpace ℝ (Fin d))),
      (∀ hist, A hist ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (kappa k * DX)) →
      ((∀ t ∈ Finset.Icc 1 T,
          IntervalToDynamic.SatisfiesAssumptions .convex X DX G (f t) (g t)) →
        ∀ R : ℝ, 0 < R →
        HasPolynomialIntervalRegret A (Metric.closedBall 0 (kappa k * DX))
          (LossClassK k .convex DX G) T k (fun n => R * Real.sqrt n) →
        let W := fixedKWrapper k .convex X DX G A g
        (∀ t ∈ Finset.Icc 1 T, W.x t ∈ X) ∧
        ∀ u : ℕ → EuclideanSpace ℝ (Fin d),
          (∀ t ∈ Finset.Icc 1 T, u t ∈ X) →
          ∀ i ∈ Finset.Icc 1 k,
            dynamicRegret f W.x u T ≤ Cconv * R *
              (1 + normalizedVariation u T i ^ (1 / (2 * i) : ℝ)) * Real.sqrt T) ∧
      ((∀ t ∈ Finset.Icc 1 T,
          IntervalToDynamic.SatisfiesAssumptions (.expConcave alpha) X DX G (f t) (g t)) →
        ∀ R : ℝ, 0 < R →
        HasPolynomialIntervalRegret A (Metric.closedBall 0 (kappa k * DX))
          (LossClassK k (.expConcave alpha) DX G) T k
          (fun n => R * d * (1 + Real.log n)) →
        let W := fixedKWrapper k (.expConcave alpha) X DX G A g
        (∀ t ∈ Finset.Icc 1 T, W.x t ∈ X) ∧
        ∀ u : ℕ → EuclideanSpace ℝ (Fin d),
          (∀ t ∈ Finset.Icc 1 T, u t ∈ X) →
          ∀ i ∈ Finset.Icc 1 k,
            dynamicRegret f W.x u T ≤ Cexp * R *
              ((d : ℝ) + (d : ℝ) ^ (((2 * i : ℕ) : ℝ) / ((2 * i + 1 : ℕ) : ℝ)) *
                normalizedVariation u T i ^ ((2 : ℝ) / (2 * i + 1)) *
                (T : ℝ) ^ ((1 : ℝ) / (2 * i + 1)))) ∧
      ((∀ t ∈ Finset.Icc 1 T,
          IntervalToDynamic.SatisfiesAssumptions (.stronglyConvex lam) X DX G (f t) (g t)) →
        ∀ R : ℝ, 0 < R →
        HasPolynomialIntervalRegret A (Metric.closedBall 0 (kappa k * DX))
          (LossClassK k (.stronglyConvex lam) DX G) T k
          (fun n => R * (1 + Real.log n)) →
        let W := fixedKWrapper k (.stronglyConvex lam) X DX G A g
        (∀ t ∈ Finset.Icc 1 T, W.x t ∈ X) ∧
        ∀ u : ℕ → EuclideanSpace ℝ (Fin d),
          (∀ t ∈ Finset.Icc 1 T, u t ∈ X) →
          ∀ i ∈ Finset.Icc 1 k,
            dynamicRegret f W.x u T ≤ Cstrong * R *
              (1 + normalizedVariation u T i ^ ((2 : ℝ) / (2 * i + 1)) *
                (T : ℝ) ^ ((1 : ℝ) / (2 * i + 1)))) := by sorry

end IntervalToDynamic.Supplement
