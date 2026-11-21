-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_projTensor
-- name    : MasulloGRH.nuclear_projTensor
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:40:37.239652+00:00
-- url     : https://prove2.me/theorems/3afe0314-776a-4c62-899d-213caeb0e37b
-- title:
--   The projective tensor product of nuclear spaces is nuclear
-- statement:
--   Here a Hausdorff locally convex space $E$ over $\mathbb C$ is called **nuclear** if for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on the algebraic tensor product $E\otimes F$ coincide.
--
--   Let $E$ and $F$ be nuclear spaces, and let $E\otimes_\pi F$ denote the algebraic tensor product $E\otimes F$ with the projective topology, i.e. the finest locally convex topology making the canonical bilinear map $E\times F\to E\otimes F$, $(x,y)\mapsto x\otimes y$, continuous. Then
--   $$
--   E\otimes_\pi F \text{ is nuclear.}
--   $$
--   The source states this for the completion $E\hat\otimes_\pi F$; the uncompleted space is a dense subspace of it, so the two statements are equivalent by the subspace property. It is used to obtain nuclearity of tensor products of spaces of $\theta$-functions.
--
--   **Formalization Note** `IsNuclear E` includes the requirement that $E$ is Hausdorff and locally convex, and quantifies over spaces $F$ in the same universe as $E$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.10 (Permanence properties), p. 689, item 4 (projective tensor products); see also H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §7.5 (Proposition: the completed projective tensor product of two nuclear spaces is nuclear), and F. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 50, Proposition 50.1

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem nuclear_projTensor (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsNuclear E) (hF : IsNuclear F) :
    @IsNuclear (E ⊗[ℂ] F) _ _ (projTensorTopology E F) := by sorry

end MasulloGRH
