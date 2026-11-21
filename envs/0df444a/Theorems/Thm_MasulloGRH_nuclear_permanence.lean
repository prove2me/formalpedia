-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_permanence
-- name    : MasulloGRH.nuclear_permanence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T22:02:46.841404+00:00
-- url     : https://prove2.me/theorems/8fb9768d-20ed-42ed-b098-d5abbd4438d8
-- title:
--   Lemma C.2.4.10 — permanence properties of nuclearity: subspaces, quotients, products, projective tensor products
-- statement:
--   A Hausdorff locally convex space $E$ over $\mathbb C$ is **nuclear** if for every Hausdorff locally convex space $F$ the projective and the injective topology on $E\otimes F$ coincide. Nuclearity is inherited as follows.
--
--   1. Every linear subspace of a nuclear space, with the induced topology, is nuclear.
--   2. The quotient of a nuclear space by a closed linear subspace is nuclear.
--   3. The product of an arbitrary family of nuclear spaces, with the product topology, is nuclear.
--   4. If $E$ and $F$ are nuclear, then $E\otimes F$ with the projective topology is nuclear.
--
--   These rules are how the draft transfers nuclearity from Schwartz–Bruhat spaces to spaces of $\theta$-functions, their isotypes and their tensor products.
--
--   **Formalization Note** In each item the spaces involved lie in one universe. Countable direct sums, which the source also lists, are not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.10 (Permanence properties), p. 689: subspaces, Hausdorff quotients, products, binary projective tensor products

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem nuclear_permanence :
    (∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E], IsNuclear E →
      (∀ V : Submodule ℂ E, IsNuclear V) ∧
      (∀ V : Submodule ℂ E, IsClosed (V : Set E) → IsNuclear (E ⧸ V))) ∧
    (∀ (ι : Type u) (E : ι → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      [∀ i, TopologicalSpace (E i)], (∀ i, IsNuclear (E i)) → IsNuclear (∀ i, E i)) ∧
    (∀ (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsNuclear E → IsNuclear F →
      @IsNuclear (E ⊗[ℂ] F) _ _ (projTensorTopology E F)) := by sorry

end MasulloGRH
