-- Prove2me | Theorems.Thm_MasulloGRH_projTensor_assoc
-- name    : MasulloGRH.projTensor_assoc
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:57:00.72518+00:00
-- url     : https://prove2.me/theorems/2a19f05f-d05a-418b-a224-bddf7d4f4563
-- title:
--   Associativity of the projective tensor product: $(E\otimes_\pi F)\otimes_\pi G\cong E\otimes_\pi(F\otimes_\pi G)$
-- statement:
--   Throughout, all vector spaces are over $\mathbb C$, and a locally convex space is one whose topology is defined by a family of seminorms. For topological vector spaces $E,F$, the projective topology $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology making the canonical bilinear map $E\times F\to E\otimes F$, $(x,y)\mapsto x\otimes y$, continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology.
--
--   Let $E$, $F$, $G$ be Hausdorff locally convex spaces. Then the canonical algebraic isomorphism
--   $$
--   \alpha:(E\otimes F)\otimes G\to E\otimes(F\otimes G),\qquad (x\otimes y)\otimes z\mapsto x\otimes(y\otimes z),
--   $$
--   is a topological isomorphism
--   $$
--   (E\otimes_\pi F)\otimes_\pi G\;\cong\; E\otimes_\pi(F\otimes_\pi G).
--   $$
--   Equivalently, the projective topology of $(E\otimes_\pi F)\otimes G$ is the topology induced by $\alpha$ from the projective topology of $E\otimes(F\otimes_\pi G)$.
--
--   It is one of the basic structural facts about tensor product topologies and is used in proving that the projective tensor product of two nuclear spaces is nuclear.
--
--   **Formalization Note** The statement is the equality of topologies `projTensorTopology (E ⊗ F) G = induced (TensorProduct.assoc ℂ E F G) (projTensorTopology E (F ⊗ G))`, where $E\otimes F$ and $F\otimes G$ carry their projective topologies. All three spaces live in the same universe.
-- source:
--   A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Mem. AMS 16 (1955), Ch. I, §1, n°1 (associativity of the projective tensor product); H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §6 and the proof of §7.5; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 43. Used in the proof that $E\otimes_\pi F$ is nuclear for nuclear $E,F$ (Masullo, The Music of the Primes, Appendix C, Lemma C.2.4.10(4), p. 689).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem projTensor_assoc (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G) :
    @projTensorTopology (E ⊗[ℂ] F) _ _ (projTensorTopology E F) G _ _ _ =
      TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
        (@projTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (projTensorTopology F G)) := by sorry

end MasulloGRH
