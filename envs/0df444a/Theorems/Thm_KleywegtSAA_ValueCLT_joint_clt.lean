-- Prove2me | Theorems.Thm_KleywegtSAA_ValueCLT_joint_clt
-- name    : KleywegtSAA.ValueCLT.joint_clt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:37.664975+00:00
-- url     : https://prove2.me/theorems/f5e3a76f-f186-40f2-bcf6-a0772329ba39
-- title:
--   §2.2, p. 5 — (√N[ĝ_N(x) − g(x)])_{x∈T} ⇒ (Y(x))_{x∈T}, a centered Gaussian vector with the autocovariance of G(x, W)
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $G(x, \cdot)$ measurable for $x \in \mathcal S$, and $W^1, W^2, \dots$ an i.i.d. sample of $W$. Let $T \subseteq \mathcal S$ be a set of points such that the variance $\sigma^2(x) = \operatorname{Var}\{G(x, W)\}$ of (2.7) exists for every $x \in T$. Let $Y = (Y(x))_{x \in T}$ be a Gaussian random vector with mean zero and covariance
--   $$\operatorname{Cov}\big(Y(x), Y(x')\big) = \operatorname{Cov}\big(G(x, W), G(x', W)\big), \qquad x, x' \in T.$$
--   Then, as $N \to \infty$,
--   $$\Big(\sqrt N\,\big[\hat g_N(x) - g(x)\big]\Big)_{x \in T} \;\Rightarrow\; \big(Y(x)\big)_{x \in T},$$
--   where $\Rightarrow$ denotes convergence in distribution.
--
--   This is the central limit theorem step of the proof of Proposition 2.3; with $T = \mathcal S^*$ it supplies the Gaussian limit in (2.8).
--
--   **Formalization Note** The page states the CLT for $T = \mathcal S$ under finite variances on $\mathcal S$, in two sentences: marginal convergence of each coordinate to $N(0, \sigma^2(x))$ and the identification of the covariance of the limit. The proof of (2.8) uses the joint convergence of the vector, which is what is stated here, for every subfamily $T \subseteq \mathcal S$ with finite variances (so it covers both $T = \mathcal S$ and $T = \mathcal S^*$). The limit is any random vector $Y$, on any probability space, whose law is the multivariate Gaussian measure with mean $0$ and the autocovariance matrix of $G(\cdot, W)$ on $T$; that matrix is positive semidefinite under the variance hypothesis, so the Gaussian law is the genuine one. The integrability hypothesis of (1.1) is implied by the variance hypothesis on $T$ and is not repeated.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 5, §2.2, (2.7) and the two sentences following it ("Then it follows by the Central Limit Theorem (CLT) …")

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

namespace KleywegtSAA.ValueCLT

open MeasureTheory ProbabilityTheory Filter Topology

open Classical in
/-- Kleywegt–Shapiro, §2.2, p. 5 (the CLT step before Proposition 2.3): for a finite family
`T ⊆ S` of points at which `G(x, W)` has finite variance, the random vector
`(√N [ĝ_N(x) − g(x)])_{x ∈ T}` converges in distribution to a centered Gaussian vector `Y` whose
covariance matrix is the autocovariance `Cov(G(x, W), G(x', W))`, `x, x' ∈ T`. -/
theorem joint_clt
    {X : Type*} (S : Finset X)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (T : Finset X) (hT : T ⊆ S)
    (hT2 : ∀ x ∈ T, MemLp (fun ω => G x (W 0 ω)) 2 P) :
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
      (Y : Ω' → EuclideanSpace ℝ T),
      HasLaw Y (multivariateGaussian 0 (covMat G P W T)) Q →
      TendstoInDistribution (fun (N : ℕ) ω => scaledDev G P W T N ω) atTop Y (fun _ => P) Q := by sorry

end KleywegtSAA.ValueCLT
