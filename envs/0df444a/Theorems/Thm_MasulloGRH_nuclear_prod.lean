-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_prod
-- name    : MasulloGRH.nuclear_prod
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:48:24.062308+00:00
-- url     : https://prove2.me/theorems/5ea57e49-f598-47db-b82c-d97823a39108
-- title:
--   The product of two nuclear spaces is nuclear
-- statement:
--   Here a Hausdorff locally convex space $E$ over $\mathbb C$ is called **nuclear** if for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on the algebraic tensor product $E\otimes F$ coincide (Grothendieck's definition).
--
--   Let $E$ and $G$ be nuclear spaces. Then their product, with the product topology,
--   $$
--   E\times G \text{ is nuclear.}
--   $$
--
--   This is the finite case of the permanence of nuclearity under products: by induction, every finite product $E_1\times\cdots\times E_n$ of nuclear spaces is nuclear. Equivalently it is the statement for the finite direct sum $E\oplus G$, which is one of the basic building blocks for the permanence properties of nuclear spaces.
--
--   **Formalization Note** `IsNuclear E` includes the requirement that $E$ is Hausdorff and locally convex, and quantifies over spaces $F$ in the same universe as $E$. Both factors lie in the same universe; `E × G` carries the product topology.
-- source:
--   F. Trèves, Topological Vector Spaces, Distributions and Kernels (Academic Press 1967), Ch. 50, Proposition 50.1 (the product of any family of nuclear spaces is nuclear; here the case of two factors); H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §7, Proposition 7.4 (products of nuclear spaces); A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Lemma C.2.4.10, item 3, p. 689

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem nuclear_prod (E G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (hE : IsNuclear E) (hG : IsNuclear G) :
    IsNuclear (E × G) := by sorry

end MasulloGRH
