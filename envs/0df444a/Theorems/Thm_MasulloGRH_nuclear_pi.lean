-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_pi
-- name    : MasulloGRH.nuclear_pi
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:40:29.714061+00:00
-- url     : https://prove2.me/theorems/e2f9c1fc-9b28-442f-8dda-bef932c7b9bc
-- title:
--   Products of nuclear spaces are nuclear
-- statement:
--   Here a Hausdorff locally convex space $E$ over $\mathbb C$ is called **nuclear** if for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on the algebraic tensor product $E\otimes F$ coincide.
--
--   Let $(E_i)_{i\in I}$ be an arbitrary family of nuclear spaces, indexed by any set $I$ (possibly empty or uncountable). Then the product, with the product topology,
--   $$
--   \prod_{i\in I} E_i \text{ is nuclear.}
--   $$
--   For $I=\varnothing$ the product is the zero space. This permanence property is used to build nuclear spaces as products of known ones.
--
--   **Formalization Note** `IsNuclear E` includes the requirement that $E$ is Hausdorff and locally convex, and quantifies over spaces $F$ in the same universe as $E$. The index type and all factors lie in the same universe.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.10 (Permanence properties), p. 689, item 3 (products); see also H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §7.5 (Proposition: the product of an arbitrary family of nuclear spaces is nuclear), and F. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 50, Proposition 50.1

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem nuclear_pi (ι : Type u) (E : ι → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, TopologicalSpace (E i)] (hE : ∀ i, IsNuclear (E i)) : IsNuclear (∀ i, E i) := by sorry

end MasulloGRH
