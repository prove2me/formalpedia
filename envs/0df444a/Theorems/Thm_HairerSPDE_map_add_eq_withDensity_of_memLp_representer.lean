-- Prove2me | Theorems.Thm_HairerSPDE_map_add_eq_withDensity_of_memLp_representer
-- name    : HairerSPDE.map_add_eq_withDensity_of_memLp_representer
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T11:53:17.119406+00:00
-- url     : https://prove2.me/theorems/4c4f91e5-24f6-4ce0-937b-8aacf50a074e
-- title:
--   Cameron-Martin density formula for an L^2(mu) representer
-- statement:
--   **The Cameron-Martin density formula for an $L^2(\mu)$ representer.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, $h \in B$, and $h^{*} \in L^2(B,\mu)$ a reproducing element: measurable, square integrable, with $\int h^{*}\,\ell \, d\mu = \ell(h)$ for all $\ell \in B^{*}$, and lying in the closed span $R_\mu$ of the duals. Then the translate $T_h(x) = x+h$ pushes $\mu$ forward to the measure with density
--
--   $$ (T_h)_*\mu = \exp\!\Bigl(h^{*}(x) - \tfrac12 \|h^{*}\|_{L^2}^2\Bigr)\,\mu . $$
--
--   This is Hairer's Theorem 4.44 (the 'if' direction) with the explicit density of equation (4.14); the constant $\tfrac12 \|h^{*}\|_{L^2}^2$ equals $\tfrac12 \|h\|_\mu^2$ because membership of $h^{*}$ in $R_\mu$ makes it the minimal-norm representer. The exponent is finite $\mu$-a.e. and the exponential is everywhere strictly positive, so the density vanishes exactly on $\mu$-null sets; this is the positivity that upgrades absolute continuity to equality of null sets in Proposition 4.45.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Theorem 4.44 (Cameron-Martin) and equation (4.14), used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem map_add_eq_withDensity_of_memLp_representer {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'rep : ∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h)
    (h'orth : (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0)) :
    μ.map (fun x : B => x + h) =
      μ.withDensity
        (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2))) := by sorry

end HairerSPDE
