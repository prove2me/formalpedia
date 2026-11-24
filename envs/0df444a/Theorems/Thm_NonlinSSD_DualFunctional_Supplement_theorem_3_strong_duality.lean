-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_Supplement_theorem_3_strong_duality
-- name    : NonlinSSD.DualFunctional.Supplement.theorem_3_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:07:08.475658+00:00
-- url     : https://prove2.me/theorems/360552fd-d742-46b4-acdd-cd7df6ba8a46
-- title:
--   Theorem 3 (corrected: zero utilities allowed) — dual attainment, equal values and primal recovery
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be an arbitrary probability space. Let $Z$ be a convex subset of a separable locally convex Hausdorff real vector space $\mathcal Z$, with continuous operators $H,G_1,\ldots,G_m:\mathcal Z\to\mathcal L_1$ whose realizations are almost surely concave and continuous on the whole decision space. Let $Y_i\in\mathcal L_1$ be reference outcomes and $[a_i,b_i]$ the bounded dominance intervals. All these data are those of the published shared problem.
--
--   Assume uniform dominance: a common $\tilde z\in Z$ gives a strictly positive uniform gap between $F_2(Y_i;\eta)$ and $F_2(G_i(\tilde z);\eta)$ on each $[a_i,b_i]$. Fix any attained primal optimizer $(z_0,X_0)$ of (11)–(14). Write $D$ for the total supremum (30), and let $\mathcal O_D$ be the set of feasible minimizers in (31). Then
--
--   $$\mathcal O_D\ne\varnothing,\qquad D(u,\theta)=\mathbb E[H(z_0)]\quad\text{for every }(u,\theta)\in\mathcal O_D.$$
--
--   Furthermore, for every dual optimizer $(u,\theta)$ and every maximizer $(z,X)$ of $L(\cdot,\cdot,u,\theta)$ over $Z\times\mathcal L_1^m$, if
--
--   $$F_2(X_i;\eta)\le F_2(Y_i;\eta)\ (\eta\in[a_i,b_i]),\quad X_i\le G_i(z)\ \text{a.s.},$$
--   $$\mathbb E[u_i(X_i)]=\mathbb E[u_i(Y_i)],\qquad \theta_i(X_i-G_i(z))=0\ \text{a.s.}\quad(1\le i\le m),$$
--
--   then $(z,X)$ is a primal optimal solution. No existence of such a Lagrangian maximizer for every dual optimizer is asserted.
--
--   This is the paper's nonlinear split-variable strong-duality theorem. It adds dual attainment and recovery to the utility-multiplier optimality theory without restricting to finite scenarios or bounded outcomes.
--
--   **Formalization Note** All standing assumptions are carried by the shared `Problem`. Dual feasibility means only admissible utilities and nonnegative essentially bounded multipliers. The supremum is extended-real; its finiteness at dual optima is concluded, not assumed. The published correction $c\ge0$ of the utility class is retained: the printed $c>0$ would make the dual-attainment assertion false. The cone assertion on p. 7 and the measure correspondence on p. 10 support the correction; the explicit example and corrected claim are retained in DISPROOF.md.
--
--   Differences from the source:
--   - correction: the inherited utility definition on p. 7 prints $c>0$ → the published shared utility cone uses $c\ge0$; reason: the same page calls it a convex cone and p. 10 includes all nonnegative measures; with $H(z)=G(z)=z$, $Z=[0,1]$, $Y=-1$, $[a,b]=[0,2]$, strict positive slopes give dual infimum 1 without attainment, as shown in DISPROOF.md
--   - encoding: an optimal primal solution exists and both optimal values coincide → an arbitrary primal optimizer $(z_0,X_0)$ is bound and every dual optimizer has $D(u,\theta)=\mathbb E H(z_0)$ in `EReal`; reason: existence of a dual optimizer is a separate conclusion, so this names the finite common value without assuming dual attainment or a zero gap
--   - encoding: $\mathcal L_1$, $\mathcal L_\infty$, a.s. constraints, and an attained maximum in (18) → random variables are functions with `Integrable` or `MemLp` guards; `MaximizesL` contains membership and comparison with every integrable competitor; feasibility and complementarity use a.e. relations; reason: this makes the source domains and attainment explicit without restricting the probability space, decision space, or outcomes
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), pp. 11–12, Theorem 3; Eqs. (30)–(31), (12)–(14), (18)–(20), Definition 1

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Supplement_TotalDual

namespace NonlinSSD.DualFunctional.Supplement

open MeasureTheory
open NonlinSSD.Optimality

/-- Theorem 3, pp. 11–12: dual attainment, equality of attained optimal values,
and conditional recovery from every dual optimizer. The arbitrary primal optimizer
(z₀,X₀) names the finite common value; no gap or dual attainment is assumed.
The utility class inherits the published correction c ≥ 0 on p. 7. -/
theorem theorem_3_strong_duality
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (pr : Problem Ω 𝒵 P m) (hdom : pr.UniformDominance)
    (z₀ : 𝒵) (X₀ : Fin m → Ω → ℝ) (hopt : pr.IsOptimal z₀ X₀) :
    (∃ (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ),
      IsDualOptimal pr u θ) ∧
    (∀ (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ),
      IsDualOptimal pr u θ →
      totalDual pr u θ = ((∫ ω, pr.H z₀ ω ∂P : ℝ) : EReal)) ∧
    (∀ (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ),
      IsDualOptimal pr u θ →
      ∀ (z : 𝒵) (X : Fin m → Ω → ℝ),
      pr.MaximizesL z X u θ → pr.Dominates X →
      (∀ i, X i ≤ᵐ[P] pr.G i z) →
      pr.Complementary z X u θ → pr.IsOptimal z X) := by sorry

end NonlinSSD.DualFunctional.Supplement
