-- Prove2me | Theorems.Thm_MasulloGRH_lcInductiveTopology_eq_locallyConvexFinalTopology
-- name    : MasulloGRH.lcInductiveTopology_eq_locallyConvexFinalTopology
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:52.512798+00:00
-- url     : https://prove2.me/theorems/bc9f35c7-9c2c-467e-b922-418badd96fd7
-- title:
--   The locally convex inductive topology is the topology of all seminorms that are continuous on every stage (bridge between the two platform encodings)
-- statement:
--   **Seminorm description of the locally convex inductive topology.** Let $E$ be a complex vector space, $(E_\alpha)_{\alpha\in A}$ a family of topological vector spaces over $\mathbb C$ (locally convex spaces in the applications) and $f_\alpha\colon E_\alpha\to E$ linear maps. Let $\tau$ be the *locally convex inductive topology* on $E$ defined by the $f_\alpha$: the finest locally convex vector space topology on $E$ for which every $f_\alpha$ is continuous. (For $E=\bigoplus_\alpha E_\alpha$ and the canonical injections this is the locally convex direct sum topology; for $E=\varinjlim E_\alpha$ and the canonical maps it is the locally convex inductive limit topology.)
--
--   Then $\tau$ coincides with the topology $\tau'$ on $E$ defined by the family of **all** seminorms $p$ on $E$ such that $p\circ f_\alpha$ is continuous on $E_\alpha$ for every $\alpha$ (a base of $0$-neighbourhoods of $\tau'$ consists of the finite intersections of the sets $\{x: p(x)<\varepsilon\}$ for such $p$ and $\varepsilon>0$):
--   $$\tau=\tau'.$$
--
--   Both descriptions of the inductive topology are classical, and both are used as *definitions* on the platform: the first one in `MasulloGRH.IsStrictLF`, `MasulloGRH.IsLF` and related predicates, the second one (`RiemannMasullo.locallyConvexFinalTopology`) in `RiemannMasullo.IsInjectiveLCLimit`. This theorem identifies them, so that results stated for one encoding of a locally convex inductive limit can be transported to the other.
--
--   **Formalization Note.** The left-hand side is `sInf` of the set of topologies that are locally convex (`MasulloGRH.IsLocallyConvexTopology`) and make every `f a` continuous; the right-hand side is the topology of the module filter basis of the seminorm family `{p : Seminorm ℂ E // ∀ a, Continuous (p ∘ f a)}`. The stages are assumed to be topological vector spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 662-663, Example C.1.4.6(4) and the opening of §C.1.5; classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, p. 54 (as cited by the paper)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem lcInductiveTopology_eq_locallyConvexFinalTopology (E : Type*)
    [AddCommGroup E] [Module ℂ E] {ι : Type*} (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E) :
    sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)} =
      RiemannMasullo.locallyConvexFinalTopology f := by sorry

end MasulloGRH
