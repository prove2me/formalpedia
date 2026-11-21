-- Prove2me | Theorems.Thm_MasulloGRH_finestLC_descriptions
-- name    : MasulloGRH.finestLC_descriptions
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:40:47.852442+00:00
-- url     : https://prove2.me/theorems/10dd2671-f9ce-46d3-8bfe-e36b84867b0e
-- title:
--   Proposition C.2.5.1(1) — two descriptions of the finest locally convex topology
-- statement:
--   Let $E$ be a complex vector space and $\tau$ its **finest locally convex topology**, i.e. the supremum (finest common refinement) of all locally convex vector space topologies on $E$. Proposition C.2.5.1(1) of the source gives two descriptions of $\tau$:
--
--   1. $\tau$ is the topology defined by the family of **all** seminorms on $E$;
--   2. $\tau$ is the locally convex inductive limit of all finite-dimensional subspaces of $E$, each carrying its unique Hausdorff vector space topology. That is,
--
--   $$\tau=\text{the finest locally convex topology on }E\text{ for which every inclusion }V\hookrightarrow E,\ \dim V<\infty,\text{ is continuous.}$$
--
--   These descriptions are the starting point for all further properties of $\tau$ in §C.2.5 (automatic continuity of linear maps, closed complemented subspaces, bounded sets), which the source applies to spaces of Schwartz–Bruhat functions at finite places.
--
--   **Formalization Note.** The hypothesis is the mission predicate `HasFinestLocallyConvexTopology E`. The first conclusion is Mathlib's `WithSeminorms` for the identity family indexed by `Seminorm ℂ E`. In the second, the "unique Hausdorff vector space topology" on a finite-dimensional subspace $V$ is expressed by quantifying over every Hausdorff topological vector space topology $\sigma$ on $V$ (there is exactly one), and the inductive limit topology is the infimum, in Lean's order on topologies, of the admissible locally convex topologies.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Proposition C.2.5.1(1), p. 691.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u v

theorem finestLC_descriptions (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E) :
    WithSeminorms (fun p : Seminorm ℂ E => p : SeminormFamily ℂ E (Seminorm ℂ E)) ∧
    ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧
        ∀ (V : Submodule ℂ E), FiniteDimensional ℂ V → ∀ σ : TopologicalSpace V,
          @T2Space V σ → @IsTopologicalAddGroup V σ _ → @ContinuousSMul ℂ V _ _ σ →
          @Continuous V E σ t Subtype.val} := by sorry

end MasulloGRH
