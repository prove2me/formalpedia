-- Prove2me | Theorems.Thm_MasulloGRH_projTensor_isHLCS
-- name    : MasulloGRH.projTensor_isHLCS
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:56:56.176302+00:00
-- url     : https://prove2.me/theorems/e8f033ae-7d36-4198-ace6-e79dade9628b
-- title:
--   The projective tensor product of Hausdorff locally convex spaces is Hausdorff locally convex
-- statement:
--   Throughout, all vector spaces are over $\mathbb C$, and a locally convex space is one whose topology is defined by a family of seminorms. For topological vector spaces $E,F$, the projective topology $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology making the canonical bilinear map $E\times F\to E\otimes F$, $(x,y)\mapsto x\otimes y$, continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology.
--
--   Let $E$ and $F$ be Hausdorff locally convex spaces. Then $E\otimes_\pi F$ is a Hausdorff locally convex space.
--
--   It is one of the basic structural facts about tensor product topologies and is used in proving that the projective tensor product of two nuclear spaces is nuclear.
--
--   **Formalization Note** `IsHLCS` means: the topology is given by a family of seminorms (`WithSeminorms`) and is $T_2$. The two spaces live in the same universe.
-- source:
--   A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Mem. AMS 16 (1955), Ch. I, §1, n°1; H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §6.1 (the projective tensor product $E\otimes_\pi F$ of Hausdorff locally convex spaces is Hausdorff); F. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 43. Used in the proof that $E\otimes_\pi F$ is nuclear for nuclear $E,F$ (Schaefer III.7.5; Masullo, The Music of the Primes, Appendix C, Lemma C.2.4.10(4), p. 689).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem projTensor_isHLCS (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    @IsHLCS (E ⊗[ℂ] F) _ _ (projTensorTopology E F) := by sorry

end MasulloGRH
