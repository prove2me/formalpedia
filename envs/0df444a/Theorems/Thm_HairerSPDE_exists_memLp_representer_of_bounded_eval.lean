-- Prove2me | Theorems.Thm_HairerSPDE_exists_memLp_representer_of_bounded_eval
-- name    : HairerSPDE.exists_memLp_representer_of_bounded_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T12:17:18.697463+00:00
-- url     : https://prove2.me/theorems/4133f9df-9393-4a06-9cab-c98e84bb0616
-- title:
--   Frechet-Riesz representer in the closed dual span from a bounded evaluation
-- statement:
--   **Frechet-Riesz representer in the closed dual span from a bounded evaluation.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$. If evaluation at $h$ is bounded on the duals in the $L^2(\mu)$ seminorm, $|\ell(h)| \le C\,\|\ell\|_{L^2(\mu)}$, then there is a Borel-measurable $h^* \in L^2(B,\mu)$ with $\int_B h^*\ell\,d\mu = \ell(h)$ for every $\ell \in B^*$ and lying in the closed span $R_\mu$ of the duals. This is the Frechet-Riesz step of Hairer's Theorem 4.44: the bound extends evaluation to a continuous linear functional on the Hilbert closure $R_\mu \subseteq L^2(\mu)$, represented by inner product with a unique $h^* \in R_\mu$. Membership in $R_\mu$ is recorded in the elementary form '$h^*$ is orthogonal to every $g$ orthogonal to all duals', i.e. $h^* \in (R_\mu^\perp)^\perp = R_\mu$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Section 4.2: the reproducing-kernel space R_mu of Theorem 4.44, used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem exists_memLp_representer_of_bounded_eval {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (C : ℝ) (hC : ∀ L : StrongDual ℝ B, |L h| ≤ C * (eLpNorm (fun x => L x) 2 μ).toReal) :
    ∃ h' : B → ℝ, Measurable h' ∧ MemLp h' 2 μ ∧
      (∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h) ∧
      (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0) := by sorry

end HairerSPDE
