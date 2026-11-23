-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_theorem_3
-- name    : MaxSpectralRisk.Duality.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:16:59.55058+00:00
-- url     : https://prove2.me/theorems/8c3b2607-2ba3-41c3-b67f-1f9cd7950de8
-- title:
--   Theorem 3 (companion theorem; not used in the proof of the goal) — Hadamard derivative and empirical limit law
-- statement:
--   Fix $\alpha\in(0,1)$ and a loss matrix $L$ on finite nonempty spaces. Let $K$ be the product of the probability simplices, let $\mathcal V$ be all extreme points of the normalized dual polyhedron in (16), and let $I(\mu,\nu)$ be the extreme points minimizing the dual objective at $(\mu,\nu)$.
--
--   1. At every $(\mu,\nu)\in K$, the MES value from (11) is finite and Hadamard directionally differentiable tangentially to $K$, with
--   $$
--   V'_\alpha(\mu,\nu;h_\mu,h_\nu)=\min_{(\varphi,\psi,\rho,\beta)\in I(\mu,\nu)}
--   \bigl(\varphi\cdot h_\mu+\psi\cdot h_\nu\bigr).
--   $$
--   The active set is finite and nonempty and the minimum is attained in every direction. The derivative is continuous and may be nonlinear.
--
--   2. Let $\mu_N,\nu_N$ be empirical probability vectors from two independent i.i.d. samples, both of size $N$, from $\mu,\nu$. Let $Z_X,Z_Y$ be independent centered Gaussian vectors with the covariance matrices $\Sigma_\mu,\Sigma_\nu$ specified by (17). Then
--   $$
--   \sqrt N\bigl(V_\alpha(\mu_N,\nu_N)-V_\alpha(\mu,\nu)\bigr)
--   \ \Rightarrow\ V'_\alpha(\mu,\nu;Z_X,Z_Y).
--   $$
--   No interiority, dual-optimizer uniqueness or covariance nonsingularity is assumed. This companion theorem determines the first-order sensitivity and the empirical limiting law of the finite MES.
--
--   Differences from the source:
--   - encoding: finite spaces admitting marginal probability distributions → Fin (m+1) and Fin (n+1), with the published IsDist predicate and K containing its boundary; reason: probability distributions force nonempty carriers; relabeling preserves all matrices and includes singleton carriers
--   - encoding: V_alpha and the minimum over I(mu,nu) in (18) → the real coordinate of the primal EReal MES, with finiteness and finite nonempty active-set attainment asserted explicitly; reason: the real conversions and real infimum are only used where they give the true finite values
--   - encoding: Hadamard directional differentiability tangentially to K → continuous derivative and convergence for every positive step sequence tending to zero and every converging direction sequence with feasible perturbed points; reason: this is the finite-dimensional sequential Hadamard definition, including boundary tangents and nonlinear derivatives
--   - encoding: independent random samples of size N from each marginal and independent centered Gaussian limits with (17) → independence within and between the full sample sequences, measurable marginal laws, Mathlib Gaussian laws with coordinate means and covariances, and TendstoInDistribution; reason: these express the same i.i.d. samples and weak limiting law and allow singular Gaussian covariance
--   - encoding: positive sample sizes N=1,2,... → sample size k+1 with k a natural number, for both samples; reason: this reindexes the entire positive sequence and avoids the undefined size-zero empirical measure
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 19 (continued p. 20), Theorem 3

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Finite
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Sampling

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 3, pp. 19–20, both parts. The value is the MES (11), the active set
uses all extreme points of the normalized dual, and the empirical samples are
independent i.i.d. samples with a common sample size. No uniqueness of the dual
optimizer, positivity of the marginal coordinates, or nonsingularity is assumed. -/
theorem theorem_3 {m n : ℕ} (α : ℝ) (hα : 0 < α ∧ α < 1)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) :
    (∀ θ ∈ (K : Set (Marginals m n)),
      (∃ v : ℝ, finiteV α L θ = (v : EReal)) ∧
      (active α L θ).Finite ∧ (active α L θ).Nonempty ∧
      (∀ h : Marginals m n, ∃ z ∈ active α L θ,
        derivativeV α L θ h = dualSlope z h ∧
          ∀ z' ∈ active α L θ, dualSlope z h ≤ dualSlope z' h) ∧
      HasHadamardWithin (realV α L) K θ (derivativeV α L θ)) ∧
    (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q],
      ∀ θ ∈ (K : Set (Marginals m n)),
      ∀ (X : ℕ → Ω → Fin (m + 1)) (Y : ℕ → Ω → Fin (n + 1)),
        IndependentSamples P θ X Y →
        ∀ (ZX : Ω' → Fin (m + 1) → ℝ) (ZY : Ω' → Fin (n + 1) → ℝ),
          MultinomialGaussian Q θ.1 ZX → MultinomialGaussian Q θ.2 ZY →
          IndepFun ZX ZY Q →
          TendstoInDistribution
            (fun (k : ℕ) ω => Real.sqrt ((k : ℝ) + 1) *
              (realV α L (empirical X k ω, empirical Y k ω) - realV α L θ))
            atTop (fun ω => derivativeV α L θ (ZX ω, ZY ω)) (fun _ => P) Q) := by sorry

end MaxSpectralRisk.Duality.Supplement
