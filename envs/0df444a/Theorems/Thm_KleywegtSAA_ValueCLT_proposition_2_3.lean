-- Prove2me | Theorems.Thm_KleywegtSAA_ValueCLT_proposition_2_3
-- name    : KleywegtSAA.ValueCLT.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:08.294552+00:00
-- url     : https://prove2.me/theorems/bb9ab718-c272-4ad0-b8bf-49d23fa71e5e
-- title:
--   Proposition 2.3, (2.8), p. 5 — √N(v̂_N − v*) ⇒ min_{x∈𝒮*} Y(x), Y a centered Gaussian vector with the autocovariance of G(x, W)
-- statement:
--   Consider the stochastic program $\min_{x \in \mathcal S} \{ g(x) = \mathbb E\, G(x, W) \}$ of (1.1) over a nonempty finite set $\mathcal S$, where for every $x \in \mathcal S$ the function $G(x, \cdot)$ is measurable and $\mathbb E\,|G(x, W)| < \infty$. Let $W^1, W^2, \dots$ be an i.i.d. sample of $W$, let
--   $$\hat g_N(x) = \frac1N \sum_{n=1}^N G(x, W^n), \qquad \hat v_N = \min_{x \in \mathcal S} \hat g_N(x), \qquad v^* = \min_{x \in \mathcal S} g(x),$$
--   and let $\mathcal S^*$ be the set of optimal solutions of (1.1).
--
--   **Proposition 2.3.** Suppose that the variances $\sigma^2(x) = \operatorname{Var}\{G(x, W)\}$ exist for every $x \in \mathcal S^*$. Then
--   $$\sqrt N\,(\hat v_N - v^*) \;\Rightarrow\; \min_{x \in \mathcal S^*} Y(x), \tag{2.8}$$
--   where $\Rightarrow$ denotes convergence in distribution and $(Y(x))_{x \in \mathcal S^*}$ is a Gaussian random vector with zero mean and the autocovariance function of $G(x, W)$: $\operatorname{Cov}(Y(x), Y(x')) = \operatorname{Cov}(G(x, W), G(x', W))$ for $x, x' \in \mathcal S^*$.
--
--   The result gives the first-order asymptotic distribution of the SAA estimator of the optimal value of a discrete stochastic program. When the true problem has several optimal solutions, the limit is the minimum of a correlated Gaussian vector, which has negative mean; so $\hat v_N$ is biased downward at the order $N^{-1/2}$.
--
--   **Formalization Note** The limit is any random vector $Y$, on any probability space, whose law is the multivariate Gaussian measure on $\mathbb R^{\mathcal S^*}$ with mean $0$ and covariance matrix $\big(\operatorname{Cov}(G(x, W), G(x', W))\big)_{x, x' \in \mathcal S^*}$; this matrix is positive semidefinite under the variance hypothesis, so the Gaussian law is the genuine one. The vector is indexed by $\mathcal S^*$, not by $\mathcal S$. "The variance exists" is square integrability of $G(x, W)$, assumed only on $\mathcal S^*$ as in the Proposition; off $\mathcal S^*$ only the integrability of (1.1) is assumed. "$G(x, \cdot)$ is $P$-measurable" is read as Borel measurability. The sample is a $0$-indexed sequence of independent random elements, each with the law of the first one.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 5, Proposition 2.3, (2.8); standing assumptions p. 1 (1.1) and p. 2 (2.1)

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

namespace KleywegtSAA.ValueCLT

open MeasureTheory ProbabilityTheory Filter Topology

open Classical in
/-- Kleywegt–Shapiro, Proposition 2.3, (2.8), p. 5: if the variances `σ²(x) = Var G(x, W)` exist
for every `x ∈ S*`, then `√N (v̂_N − v*) ⇒ min_{x ∈ S*} Y(x)`, where `(Y(x))_{x ∈ S*}` is a
centered Gaussian vector with the autocovariance function of `G(x, W)`. -/
theorem proposition_2_3
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P)
    (hvar : ∀ x ∈ optSet S hS (KleywegtSAA.ExpRate.trueObj G P W), MemLp (fun ω => G x (W 0 ω)) 2 P) :
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
      (Y : Ω' → EuclideanSpace ℝ (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W))),
      HasLaw Y (multivariateGaussian 0 (covMat G P W (optSet S hS (KleywegtSAA.ExpRate.trueObj G P W)))) Q →
      TendstoInDistribution
        (fun (N : ℕ) ω => Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - S.inf' hS (KleywegtSAA.ExpRate.trueObj G P W)))
        atTop
        (fun ω' => Finset.univ.inf'
          (Finset.univ_nonempty_iff.2 (optSet_nonempty S hS (KleywegtSAA.ExpRate.trueObj G P W)).to_subtype)
          (fun x => Y ω' x))
        (fun _ => P) Q := by sorry

end KleywegtSAA.ValueCLT
