-- Prove2me | Theorems.Thm_MarketInterferenceAudit_FluidLimit_theorem_1_full
-- name    : MarketInterferenceAudit.FluidLimit.theorem_1_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:54.021913+00:00
-- url     : https://prove2.me/theorems/e81e7021-4888-42c8-a24d-eb69fedf542b
-- title:
--   Theorem 1 — matching fluid limit (corrected: unit-scale normalization; optimizer uniqueness)
-- statement:
--   Let $N$ be any finite capacitated matching network with real arc values and nonnegative real capacities, demand and supply rates $\lambda_i,\pi_j\ge0$, and arrivals $(D^n,S^n)$ on a probability space with the independent-coordinate Poisson law at each positive integer density $n$. Write $\Phi_n(d,s)$ for (2), with capacity $nk_e$, and $\Phi=\Phi_1$. Each scaled random value is integrable, and without assuming uniqueness,
--
--   $$\lim_{n\to\infty}\mathbb E\!\left[\frac1n\Phi_n(D^n,S^n)\right]=\Phi(\lambda,\pi).$$
--
--   For the optimizer clause only, let $x^*$ be the unique actual primal optimum and $q^*=(a^*,b^*,m^*,\xi^*)$ the unique actual dual optimum of $\Phi(\lambda,\pi)$ and (5) at scale 1. For every choice of primal flows $X^n$ and dual tuples $Q^n=(A^n,B^n,M^n,\Xi^n)$ that are optimal almost surely at each density for the scale-1 programs with normalized inputs $(D^n/n,S^n/n)$,
--
--   $$P\!\left\{X^n\to x^*,\ A^n\to a^*,\ B^n\to b^*,\ M^n\to m^*,\ \Xi^n\to\xi^*\right\}=1.$$
--
--   Every coordinate is included on a common conull event. There is no uniqueness requirement at finite densities, no nondegeneracy or basis-selection hypothesis, and no restriction to bipartite or acyclic networks. Zero rates and zero capacities are allowed. All density couplings with the prescribed marginal laws are covered, including the source Poisson processes. This complete fluid limit identifies the allocation and every price family as well as the objective.
--
--   **Formalization Note** The sequence index is $r=n-1$, so every denominator is the positive integer $r+1$. Optimality is feasibility and optimization of the actual objective, not equality to an assigned value. The integrability assertion rules out a default-zero reading of the expectation. Uniqueness and the selectors occur inside the optimizer conjunct, after the unconditional expected-value limit.
--
--   Differences from the source:
--   - correction: Theorem 1 uses the density-scaled LP for normalized optimizer inputs → the normalized optimizer LP has scale 1, with capacities k; reason: C1: one arc with v=k=1 and rates λ=2, π=3 has unique fluid primal x*=1 and dual (a,b,ξ)=(0,0,1), but the printed normalized LP has optima tending to 2 and (1,0,0); Lemma 1 and pp. 39–40 use unit scale
--   - correction: the optimizer sentence on p. 12 has no explicit limiting uniqueness condition → fluid primal and dual uniqueness qualify only optimizer convergence; the expectation clause is unconditional; reason: C2: two equal-value arcs with k₁=k₂=2, λ=1, π₁=π₂=1 admit alternating optimal flows tending to (1,0) and (0,1); even with β=4, ρ=1/2 the experiment at demand 3 has unique primal and dual optima; the qualification is explicit on p. 39
--   - reading: Poisson arrivals per type and independent request realizations → independent demand and supply count coordinates at each density via the published fluidLaw; reason: the independent-arrival reading is used in §C.1 when sums of counts are asserted Poisson; no independence across densities is imposed
--   - generalization: counts obtained from Poisson processes and their optimal solutions → any common-space coupling with the specified within-density laws and arbitrary selectors optimal almost surely at each density, with no selector measurability restriction; reason: the paper’s process counts and random optimal solutions satisfy this interface; the conclusion is on a common conull set and needs no measurability assumption on the selections
--   - generalization: a finite directed graph with supply and demand type lists → the published finite indexed-arc network, allowing parallel arcs and empty finite type families; reason: every source graph is included by indexing its arcs and nodes; parallel arcs and empty families preserve the same finite-dimensional LP interpretation
--   - encoding: positive integer densities n and one-based demand and supply indices → sequence index r denotes density r+1 and types are Fin nd and Fin ns; reason: enumerates exactly all positive integer densities and the same finite coordinates, with no division by zero
--   - encoding: finite matching expectations and maxima of the actual programs (2) and (5) → explicit integrability conclusion and the published real supremum and feasible-minimizer predicates; reason: zero is feasible and finite capacities give a compact primal feasible set and a bounded objective; the target cannot use the integral’s nonintegrable default or an empty/unbounded real supremum
--   - encoding: almost-sure convergence of primal and dual vectors → all primal coordinates and all a, b, m, ξ coordinates converge on one common almost-everywhere event; reason: finite-dimensional vector convergence is equivalent to coordinate convergence; per-density almost-sure optimality has one common conull realization set because densities are countable
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, https://arxiv.org/abs/2205.02274v4, Theorem 1, (7), p. 12, all clauses; corrections from Lemma 1, (27), pp. 37–38, and §C.1, pp. 39–40; model (2)/(5), pp. 7/10

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidLimit_PoissonCounts
import Definitions.Def_MarketInterferenceAudit_FluidLimit_Arrivals

open MeasureTheory Filter MarketInterference.FluidBias

namespace MarketInterferenceAudit.FluidLimit

/-- arXiv:2205.02274v4, Theorem 1, (7), p. 12, with all optimizer conclusions.
Corrections: the normalized optimizer LP has scale 1 (not the printed density subscript);
only optimizer convergence is qualified by fluid primal/dual uniqueness, as on p. 39.
The expected-value conclusion is unconditional on uniqueness. Arbitrary common-space couplings
with the prescribed count law and arbitrary optimal selections are allowed. Integrability is
a conclusion, not an extra assumption. Index `r` runs through densities `r+1`. -/
theorem theorem_1_full {nd ns : ℕ} {I E : Type} [Fintype I] [Fintype E]
    [DecidableEq I] (N : Network nd ns I E)
    (lam : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hpi : ∀ j, 0 ≤ pi j)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Arrivals P lam pi) :
    (∀ r, Integrable (R.scaledValue N r) P) ∧
    Tendsto (fun r => ∫ ω, R.scaledValue N r ω ∂P) atTop (nhds (Phi N 1 lam pi)) ∧
    (∀ (xstar : E → ℝ) (qstar : DualVar nd ns I E),
      IsOptimal N 1 lam pi xstar →
      (∀ x, IsOptimal N 1 lam pi x → x = xstar) →
      IsOptimalDual N 1 lam pi qstar →
      (∀ q, IsOptimalDual N 1 lam pi q → q = qstar) →
      ∀ (X : ℕ → Ω → E → ℝ) (Q : ℕ → Ω → DualVar nd ns I E),
        (∀ r, ∀ᵐ ω ∂P, IsOptimal N 1 (R.demand r ω) (R.supply r ω) (X r ω)) →
        (∀ r, ∀ᵐ ω ∂P, IsOptimalDual N 1 (R.demand r ω) (R.supply r ω) (Q r ω)) →
        ∀ᵐ ω ∂P,
          (∀ e, Tendsto (fun r => X r ω e) atTop (nhds (xstar e))) ∧
          (∀ i, Tendsto (fun r => (Q r ω).a i) atTop (nhds (qstar.a i))) ∧
          (∀ j, Tendsto (fun r => (Q r ω).b j) atTop (nhds (qstar.b j))) ∧
          (∀ u, Tendsto (fun r => (Q r ω).m u) atTop (nhds (qstar.m u))) ∧
          (∀ e, Tendsto (fun r => (Q r ω).ξ e) atTop (nhds (qstar.ξ e)))) := by sorry

end MarketInterferenceAudit.FluidLimit
