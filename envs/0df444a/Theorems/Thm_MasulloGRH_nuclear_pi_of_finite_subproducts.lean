-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_pi_of_finite_subproducts
-- name    : MasulloGRH.nuclear_pi_of_finite_subproducts
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:48:20.949072+00:00
-- url     : https://prove2.me/theorems/05d173b9-6a9c-43ec-b335-6b24c0d88ef1
-- title:
--   A product is nuclear if all its finite subproducts are
-- statement:
--   Here a Hausdorff locally convex space $E$ over $\mathbb C$ is called **nuclear** if for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on the algebraic tensor product $E\otimes F$ coincide (Grothendieck's definition).
--
--   Let $(E_i)_{i\in I}$ be a family of Hausdorff locally convex spaces indexed by an arbitrary set $I$ (possibly empty or uncountable). For a finite subset $J\subseteq I$ write $E_J=\prod_{j\in J}E_j$ for the finite subproduct, with the product topology. If every finite subproduct $E_J$ is nuclear, then the full product, with the product topology,
--   $$
--   \prod_{i\in I}E_i \text{ is nuclear.}
--   $$
--
--   This expresses that the product $\prod_{i\in I}E_i$ is the projective limit of its finite subproducts $E_J$ ($J$ finite), and that nuclearity passes from the finite subproducts to the full product. Together with the stability of nuclearity under finite products it yields that arbitrary products of nuclear spaces are nuclear.
--
--   **Formalization Note** `IsNuclear E` includes the requirement that $E$ is Hausdorff and locally convex, and quantifies over spaces $F$ in the same universe as $E$; `IsHLCS` means Hausdorff and locally convex. The index type and all factors lie in the same universe. A finite subproduct is indexed by a `Finset` $J$ of $I$, viewed as a type. For $I=\varnothing$ the only finite subproduct is the zero space.
-- source:
--   F. Trèves, Topological Vector Spaces, Distributions and Kernels (Academic Press 1967), Ch. 50, Proposition 50.1 and its proof (products of nuclear spaces); H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §7, Proposition 7.4 and its proof (the product as projective limit of its finite subproducts; nuclearity of projective limits); A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Lemma C.2.4.10, item 3, p. 689

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem nuclear_pi_of_finite_subproducts (ι : Type u) (E : ι → Type u)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)]
    (hE : ∀ i, IsHLCS (E i)) (hJ : ∀ J : Finset ι, IsNuclear (∀ j : J, E j)) :
    IsNuclear (∀ i, E i) := by sorry

end MasulloGRH
