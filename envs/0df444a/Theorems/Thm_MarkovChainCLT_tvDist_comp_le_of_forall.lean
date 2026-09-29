-- Prove2me | Theorems.Thm_MarkovChainCLT_tvDist_comp_le_of_forall
-- name    : MarkovChainCLT.tvDist_comp_le_of_forall
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:57:43.611013+00:00
-- url     : https://prove2.me/theorems/b19f9e70-4e44-4df4-9f5c-1d6ef562ace0
-- title:
--   A pointwise total-variation bound transfers to every initial distribution
-- statement:
--   Let $K$ be a Markov kernel from $\mathsf X$ to $\mathsf Y$, let $\nu$ be a probability measure on $\mathsf Y$, and suppose
--
--   $$\bigl\|K(x,\cdot) - \nu\bigr\| \;\le\; C \qquad \text{for every } x \in \mathsf X.$$
--
--   Then for **every** initial distribution $\lambda$ on $\mathsf X$,
--
--   $$\bigl\|K\!\circ\!\lambda - \nu\bigr\| \;\le\; C.$$
--
--   **What it does.** A bound holding from every deterministic start automatically holds from every random start, with the *same* constant — averaging over the starting point cannot degrade a uniform bound. This is the step that converts uniform ergodicity, which is stated pointwise in $x$,
--   $$\|P^n(x,\cdot)-\pi\| \le R\,t^n \quad \text{for all } x,$$
--   into the statement about an arbitrary initial distribution,
--   $$\|\lambda P^n - \pi\| \le R\,t^n,$$
--   which is the form actually needed to compare a chain started from $\lambda$ with the stationary chain.
--
--   **Why this matters for the CLT.** The Markov chain central limit theorem asserts convergence *for every initial distribution*, whereas its proof establishes the limit for the stationary chain. Bridging the two is exactly this bound followed by data processing: $\|\lambda P^m - \pi\| \le Rt^m$ transfers to path space as $\|\mathbb P_{\lambda P^m} - \mathbb P_\pi\| \le R t^m$, so the chain started from $\lambda$ and observed from time $m$ onwards is geometrically close, in total variation, to the stationary chain. Since the normalized partial sums are asymptotically insensitive to discarding finitely many initial terms, the stationary limit law transfers.
--
--   **Contrast with data processing.** The companion inequality $\|K\!\circ\!\mu - K\!\circ\!\nu\| \le \|\mu-\nu\|$ compares two *pushed-forward* measures and is a contraction statement. Here instead the target $\nu$ is fixed and the hypothesis is a *uniform* pointwise bound; the conclusion keeps the same constant rather than contracting. The two are used in sequence, and neither implies the other.
--
--   **Proof.** For a measurable $B \subseteq \mathsf Y$, put $g(x) = K(x,B)$, a measurable function with values in $[0,1]$. By hypothesis $|g(x) - \nu(B)| \le \|K(x,\cdot)-\nu\| \le C$ for every $x$. Since $(K\!\circ\!\lambda)(B) = \int g\,\mathrm{d}\lambda$ and $\lambda$ is a probability measure, $\nu(B) = \int \nu(B)\,\mathrm{d}\lambda$, so
--   $$\bigl|(K\!\circ\!\lambda)(B) - \nu(B)\bigr| \;=\; \Bigl|\int \bigl(g - \nu(B)\bigr)\mathrm{d}\lambda\Bigr| \;\le\; \int \bigl|g - \nu(B)\bigr|\,\mathrm{d}\lambda \;\le\; \int C \,\mathrm{d}\lambda \;=\; C.$$
--   Taking the supremum over $B$ gives the claim.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16; D. A. Levin and Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Ch. 4; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Corollary 5.

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal

theorem MarkovChainCLT.tvDist_comp_le_of_forall {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (lam : Measure X) [IsProbabilityMeasure lam]
    (ν : Measure Y) [IsProbabilityMeasure ν] (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, tvDist (K x) ν ≤ C) :
    tvDist (K ∘ₘ lam) ν ≤ C := by sorry
