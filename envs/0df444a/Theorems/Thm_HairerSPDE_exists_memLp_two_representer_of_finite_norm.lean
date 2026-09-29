-- Prove2me | Theorems.Thm_HairerSPDE_exists_memLp_two_representer_of_finite_norm
-- name    : HairerSPDE.exists_memLp_two_representer_of_finite_norm
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T11:53:09.079205+00:00
-- url     : https://prove2.me/theorems/b0abace1-4071-4ccb-8f6b-5465f601b877
-- title:
--   The L^2(mu) reproducing element of a finite Cameron-Martin norm vector
-- statement:
--   **The $L^2(\mu)$ reproducing element of a finite Cameron-Martin norm vector.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$ with $\|h\|_\mu \neq \infty$. Let $R_\mu \subseteq L^2(B,\mu)$ be the closed linear span of the continuous linear functionals (each $\ell \in B^*$ is square-integrable for a Gaussian $\mu$). Then there is a Borel-measurable $h^{*} \in R_\mu$ with
--
--   $$ \int_B h^{*}(x)\,\ell(x)\,\mu(dx) = \ell(h) \qquad \text{for every } \ell \in B^{*}. $$
--
--   This is the reproducing-kernel element of $h$ used in Hairer's Theorem 4.44 and equation (4.14). Because $\mu$ is centred, $C_\mu(\ell,\ell) = \|\ell\|_{L^2}^2$, so finiteness of $\|h\|_\mu = \sup\{\, \ell(h) : \|\ell\|_{L^2} \le 1 \,\}$ says exactly that $\ell \mapsto \ell(h)$ is a bounded linear functional on the subspace $R_\mu$ of $L^2(B,\mu)$ with operator norm $\|h\|_\mu < \infty$; the Frechet-Riesz theorem and extension from the dense subspace to its closure give $h^{*} \in R_\mu$ with the stated reproducing identity. The final conjunct records membership in $R_\mu$ in the elementary form '$h^{*}$ is orthogonal to every $g$ orthogonal to all duals', which is exactly $h^{*} \in (R_\mu^\perp)^\perp = R_\mu$. In infinite dimensions $R_\mu$ is strictly larger than the set of duals, so $h^{*}$ need not be a continuous linear functional; this is why the representer is taken in $L^2(B,\mu)$ rather than in $B^{*}$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Section 4.2: the reproducing-kernel space R_mu of Theorem 4.44 and equation (4.14), used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem exists_memLp_two_representer_of_finite_norm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∃ h' : B → ℝ, Measurable h' ∧ MemLp h' 2 μ ∧
      (∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h) ∧
      (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0) := by sorry

end HairerSPDE
