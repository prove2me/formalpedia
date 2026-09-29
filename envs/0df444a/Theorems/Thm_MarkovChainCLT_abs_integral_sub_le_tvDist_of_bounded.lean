-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist_of_bounded
-- name    : MarkovChainCLT.abs_integral_sub_le_tvDist_of_bounded
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T22:01:34.600042+00:00
-- url     : https://prove2.me/theorems/fbcf19f2-a30c-45f9-bb98-dd8f72ac6444
-- title:
--   Total variation controls integrals of any bounded function, with constant $2M$
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathsf X$ and let $g$ be measurable with $|g| \le M$ everywhere. Then
--
--   $$\left|\int g \,\mathrm{d}\mu - \int g\,\mathrm{d}\nu\right| \;\le\; 2M\,\|\mu-\nu\|.$$
--
--   **The general test-function form.** The total variation distance is defined by testing against *sets*; the companion result for $[0,1]$-valued functions extends that to indicators' convex hull. This statement removes the range restriction entirely: any bounded measurable $g$ works, at the price of the factor $2M$. The constant is sharp — for $g = M\cdot(\mathbf 1_A - \mathbf 1_{A^c})$ the two sides agree when $A$ is a Hahn set.
--
--   **Why the general form is the one needed for limit theorems.** Convergence in distribution is characterized by convergence of $\int g\,\mathrm{d}\mu_n$ for bounded *continuous* $g$ — functions with no reason to be indicators or to take values in $[0,1]$. So transferring a weak limit from one sequence of measures to another that is close in total variation requires exactly this inequality: if $\|\mu_n - \nu_n\| \to 0$ then $\int g\,\mathrm{d}\mu_n$ and $\int g\,\mathrm{d}\nu_n$ have the same limit for every bounded continuous $g$, hence $\mu_n$ and $\nu_n$ have the same weak limit.
--
--   For Markov chains this is the last analytic ingredient in the passage from the *stationary* central limit theorem to the statement for an arbitrary initial distribution. A uniformly ergodic chain satisfies $\|\mathbb P_{\lambda P^m} - \mathbb P_\pi\| \le Rt^m$ on path space, and the test function is $g\bigl(\sqrt n(\bar f_n - \mathbb E_\pi f)\bigr)$ for a bounded continuous $g$ — bounded, but taking both signs and values outside $[0,1]$.
--
--   **Proof.** If $M = 0$ then $g \equiv 0$ and both sides vanish. Otherwise rescale: $h = (g+M)/(2M)$ is measurable with values in $[0,1]$, so the $[0,1]$-valued bound applies to $h$. Since $\mu$ and $\nu$ are probability measures, $\int h\,\mathrm{d}\rho = \bigl(\int g\,\mathrm{d}\rho + M\bigr)/(2M)$ for $\rho \in \{\mu,\nu\}$, and the additive constants cancel in the difference:
--   $$\int h\,\mathrm{d}\mu - \int h\,\mathrm{d}\nu \;=\; \frac{1}{2M}\left(\int g\,\mathrm{d}\mu - \int g\,\mathrm{d}\nu\right).$$
--   Multiplying the $[0,1]$ bound by $2M$ gives the claim. That $\mu$ and $\nu$ are *probability* measures is used exactly here — with different total masses the constants would not cancel.
-- source:
--   D. A. Levin and Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Proposition 4.5; P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 1; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Corollary 5.

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open MarkovChainCLT
open scoped ENNReal NNReal

theorem MarkovChainCLT.abs_integral_sub_le_tvDist_of_bounded {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, |g x| ≤ M) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ 2 * M * tvDist μ ν := by sorry
