-- Prove2me | Theorems.Thm_MasulloGRH_lcInductiveTopology_continuous_iff
-- name    : MasulloGRH.lcInductiveTopology_continuous_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:54.216892+00:00
-- url     : https://prove2.me/theorems/6e8a7b60-8a86-4a45-ab0f-12ce9af31d68
-- title:
--   Universal property of the locally convex inductive topology: a linear map into a locally convex space is continuous iff it is continuous on every stage
-- statement:
--   **Universal property of the locally convex inductive topology.** Let $E$ be a complex vector space, $(E_\alpha)_{\alpha\in A}$ a family of topological vector spaces over $\mathbb C$ (locally convex spaces in the applications) and $f_\alpha\colon E_\alpha\to E$ linear maps. Let $\tau$ be the *locally convex inductive topology* on $E$ defined by the $f_\alpha$: the finest locally convex vector space topology on $E$ for which every $f_\alpha$ is continuous. (For $E=\bigoplus_\alpha E_\alpha$ and the canonical injections this is the locally convex direct sum topology; for $E=\varinjlim E_\alpha$ and the canonical maps it is the locally convex inductive limit topology.)
--
--   Let $G$ be a locally convex space over $\mathbb C$ and $g\colon E\to G$ a linear map. Then
--   $$g\colon(E,\tau)\to G\ \text{is continuous}\iff g\circ f_\alpha\colon E_\alpha\to G\ \text{is continuous for every }\alpha\in A.$$
--
--   This is the "expected universal mapping property" of locally convex direct sums and inductive limits recalled by the source at the beginning of §C.1.5: a linear map out of $\varinjlim E_\alpha$ (or out of $\bigoplus_\alpha E_\alpha$) into a locally convex space is continuous as soon as its restrictions to the stages are. The source uses it constantly, e.g. for the bijectivity of the duality map in Lemma C.1.6.1 and in the proof of Corollary C.1.5.13.
--
--   **Formalization Note.** $\tau$ is `sInf` of the set of locally convex topologies on `E` making all `f a` continuous (the finest such topology; same encoding as in `MasulloGRH.IsStrictLF`). Local convexity of $G$ is `MasulloGRH.IsLocallyConvexTopology`; $G$ need not be Hausdorff and may live in any universe. The stages are only assumed to be topological vector spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 662-663, Example C.1.4.6(4) and the opening of §C.1.5; classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, p. 54 (as cited by the paper)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem lcInductiveTopology_continuous_iff (E : Type*)
    [AddCommGroup E] [Module ℂ E] {ι : Type*} (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E)
    (G : Type*) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hG : IsLocallyConvexTopology G ‹TopologicalSpace G›) (g : E →ₗ[ℂ] G) :
    @Continuous E G
        (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)}) _ g ↔
      ∀ a, Continuous (fun x : X a => g (f a x)) := by sorry

end MasulloGRH
