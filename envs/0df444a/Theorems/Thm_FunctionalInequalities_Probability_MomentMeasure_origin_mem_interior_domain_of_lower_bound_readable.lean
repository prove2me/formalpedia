-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_origin_mem_interior_domain_of_lower_bound_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:59.731694+00:00
-- url     : https://prove2.me/theorems/c5c8b2a4-1168-4a59-aee9-15abcae98b6f
-- title:
--   Interior Domain at the Origin from a Lower Bound
-- statement:
--   This gives the normalization precursor for a convex potential.
--
--   Let $\mu$ be a finite Borel measure on a finite-dimensional real inner-product space. Assume:
--
--   1. $0$ lies in the interior of the convex hull of $\operatorname{supp}\mu$;
--   2. the identity map is integrable with respect to $\mu$;
--   3. $c$ is a convex potential that is potential-integrable with respect to $\mu$;
--   4. for some $M\in\mathbb R$, $-M\leq c(x)$ for every $x$.
--
--   Then
--
--   $$
--   0\in\operatorname{int}\{x:c(x)\neq+\infty\}.
--   $$
--
--   The result converts a signed lower-bounded convex potential into the nonnegative setting needed for effective-domain interior arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem origin_mem_interior_domain_of_lower_bound (μ : Measure E) [IsFiniteMeasure μ]
--       (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
--       (hfirst : Integrable (fun x : E => x) μ)
--       (c : E → EReal) (hc : ConvexPotential c) (hp : PotentialIntegrable c μ)
--       (M : ℝ) (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ c x) :
--       (0 : E) ∈ interior {x | c x ≠ ⊤}
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Normalization`](https://prove2.me/theorems/ab168678-c2b4-4a84-b64b-71e05b4b5b05).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81), [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c).
--
--   Supporting theorems: [`convex_epigraph_affineSubtract`](https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9), [`affineSubtract_potentialIntegrable`](https://prove2.me/theorems/f9035aa8-a93c-47ed-80fb-13efe5d1963a), [`mem_interior_setOf_ne_top_of_lintegral_ne_top`](https://prove2.me/theorems/41e08c8a-6e29-45a9-8d48-c23b3f6ab84d).
--
--   [Source excerpt, lines 30–35](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Normalization.lean#L30-L35) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Normalization.lean#L28-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Normalization`, declaration `FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Normalization

open FunctionalInequalities.Analysis
open MeasureTheory Filter Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound_readable (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (hfirst : Integrable (fun x : E => x) μ)
    (c : E → EReal) (hc : ConvexPotential c) (hp : PotentialIntegrable c μ)
    (M : ℝ) (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ c x) :
    (0 : E) ∈ interior {x | c x ≠ ⊤} := by sorry
