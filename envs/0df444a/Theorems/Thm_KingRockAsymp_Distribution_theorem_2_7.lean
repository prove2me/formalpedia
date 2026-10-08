-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_theorem_2_7
-- name    : KingRockAsymp.Distribution.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:55.288742+00:00
-- url     : https://prove2.me/theorems/51f4ec3d-399c-4bf9-bf28-bd8f47b25e33
-- title:
--   Theorem 2.7 — generalized M-estimates converge in distribution to $DF^{-1}(0|x^*)(-w^*)$ with $w^*$ normal
-- statement:
--   Let $s_1, s_2, \dots$ be random elements of a measurable space $S$, let $U$ be a compact neighborhood of $x^* \in \mathbb R^n$, and let $f : U \times S \to \mathbb R^m$ satisfy the probabilistic assumptions P.1–P.4 with respect to $U$:
--
--   1. $f$ is continuous in $x$ on $U$ and measurable in $s$;
--   2. the $s_i$ are independent and identically distributed;
--   3. $E|f(x,s_1)|^2 < \infty$ for some $x \in U$;
--   4. $|f(x_1,s) - f(x_2,s)| \le a(s)|x_1 - x_2|$ on $U$ for some $a$ with $E|a(s_1)|^2 < \infty$.
--
--   Let $Ef(x) = E f(x,s_1)$ and suppose $Ef$ is B-differentiable at $x^*$. Let $N : \mathbb R^n \rightrightarrows \mathbb R^m$ and $F = Ef + N$ (on $U$), and assume M.2–M.4: $\operatorname{gph} N$ is closed and $N$ is proto-differentiable at $(x^*, -Ef(x^*))$; $F$ is subinvertible at $(x^*,0)$; and the contingent derivative $DF^{-1}(0|x^*)(y)$ has at most one element for every $y$. Let $x^\nu$ be measurable maps such that, for every $\nu \ge 1$, almost surely $x^\nu$ solves the sample generalized equation
--   $$0 \in \bar f^\nu(x) + N(x), \qquad \bar f^\nu(x) = \frac1\nu \sum_{i=1}^\nu f(x,s_i), \tag{2.5}$$
--   and suppose $x^\nu \to x^*$ almost surely. Let $w^*$ be a random vector in $\mathbb R^m$ that is normally distributed with mean $0$ and covariance $\operatorname{cov} f(x^*,s_1)$. Then there is a map $L : \mathbb R^m \to \mathbb R^n$ with $L(y) \in DF^{-1}(0|x^*)(y)$ for every $y$ — so $L$ is the single-valued map $DF^{-1}(0|x^*)$ — such that
--   $$\sqrt\nu\,\big[x^\nu - x^*\big] \xrightarrow{\ \mathcal D\ } DF^{-1}(0|x^*)(-w^*).$$
--
--   This is the asymptotic distribution theory for constrained and nonsmooth M-estimates: the normalized estimation error converges to the image of a normal vector under the contingent derivative of $F^{-1}$, which is in general nonlinear, so the limit law is in general not normal.
--
--   **Formalization Note** The paper states "if a sequence $\{x^\nu\}$ of measurable selections … converges almost surely, it converges to the point $x^*$"; this fails when the true equation has another solution in $U$, so we assume that the almost sure limit is $x^*$ and drop that clause from the conclusion. The hypothesis $0 \in F(x^*)$ is part of subinvertibility. $U$ is a compact set with $x^*$ in its interior ("compact neighborhood"). Measurability of $x^\nu$ is from "measurable selections"; the selection property is required almost surely for every $\nu \ge 1$ ($\bar f^0$ is not defined). $F(x) = \emptyset$ for $x \notin U$, since $f$ is given only on $U$. The law of $w^*$ is fixed through linear functionals, as in the Appendix: for every $\ell \in \mathbb R^m$, $\langle \ell, w^*\rangle$ has the law $\mathcal N\big(0, \operatorname{Var}\langle \ell, f(x^*,s_1)\rangle\big)$, and $w^*$ lives on its own probability space. B-differentiability is (2.4); $DF^{-1}(0|x^*)$ is the contingent derivative (2.2) of $F^{-1}$, not the printed sum formula of M.4. $s_1$ is `s 0`, and $\sqrt\nu$ is `Real.sqrt ν`.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), Theorem 2.7, p. 9 (authors' manuscript pagination)

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem theorem_2_7 {n m : ℕ} {S Ω Ω' : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P] (μ' : Measure Ω')
    [IsProbabilityMeasure μ']
    (U : Set (Rn n)) (x₀ : Rn n) (hUc : IsCompact U) (hU : U ∈ 𝓝 x₀)
    (f : Rn n → S → Rn m) (s : ℕ → Ω → S) (hP : ProbabilisticAssumptions U f s P)
    (hB : ∃ D : Rn n → Rn m, HasBDerivAt (expect f s P) D x₀)
    (N : Rn n → Set (Rn m)) (hN : IsClosed (graph N))
    (hNp : IsProtoDifferentiable N x₀ (-(expect f s P x₀)))
    (hM3 : IsSubinvertibleAt (FEst U f s P N) x₀)
    (hM4 : ∀ y, (contingentDeriv (svInv (FEst U f s P N)) 0 x₀ y).Subsingleton)
    (x : ℕ → Ω → Rn n) (hx : ∀ ν, Measurable (x ν))
    (hsel : ∀ ν, 1 ≤ ν → ∀ᵐ ω ∂P,
      ∃ v ∈ N (x ν ω), empMean f s ν ω (x ν ω) + v = 0)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun ν => x ν ω) atTop (𝓝 x₀))
    (W : Ω' → Rn m) (hW : Measurable W)
    (hWlaw : ∀ ℓ : Rn m, μ'.map (fun ω' => inner ℝ ℓ (W ω')) =
      gaussianReal 0 (Var[fun ω => inner ℝ ℓ (f x₀ (s 0 ω)); P]).toNNReal) :
    ∃ L : Rn m → Rn n,
      (∀ y : Rn m, L y ∈ contingentDeriv (svInv (FEst U f s P N)) 0 x₀ y) ∧
      TendstoInDistribution (fun (ν : ℕ) ω => Real.sqrt ν • (x ν ω - x₀)) atTop
        (fun ω' => L (-(W ω'))) (fun _ => P) μ' := by sorry

end KingRockAsymp.Distribution
