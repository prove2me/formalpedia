-- Prove2me | Theorems.Thm_MasulloGRH_indTensor_le_projTensor_le_epsTensor
-- name    : MasulloGRH.indTensor_le_projTensor_le_epsTensor
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:19.07555+00:00
-- url     : https://prove2.me/theorems/8bf77abd-4a91-4952-ab90-9a84b5727f19
-- title:
--   On $E\otimes F$ the inductive topology is finer than the projective topology, which is finer than the injective topology
-- statement:
--   **Comparison of the three tensor product topologies: $\iota\ge\pi\ge\varepsilon$.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Hausdorff locally convex spaces. Then the identity maps of $E\otimes F$
--   $$E\otimes_\iota F\longrightarrow E\otimes_\pi F\longrightarrow E\otimes_\varepsilon F$$
--   are continuous: the inductive topology is finer than the projective topology, and the projective topology is finer than the injective topology.
--
--   The second map is the map (C.2.4.1) whose being a topological isomorphism for all $F$ defines nuclearity of $E$; the first is an isomorphism when $E$ and $F$ are Fréchet spaces (Corollary C.2.3.12).
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. In Mathlib's order on topologies, `t₁ ≤ t₂` means that `t₁` is finer than `t₂` (every `t₂`-open set is `t₁`-open), i.e. the identity $(X,t_1)\to(X,t_2)$ is continuous; the statement is `indTensorTopology E F ≤ projTensorTopology E F ∧ projTensorTopology E F ≤ epsTensorTopology E F`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 679 (after Proposition C.2.3.7), p. 682 (after (C.2.3.22)) and p. 685, (C.2.4.1); classical reference: F. Trèves, Topological Vector Spaces, Distributions and Kernels, Prop. 43.5 (the projective topology is finer than the injective topology)

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem indTensor_le_projTensor_le_epsTensor (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    indTensorTopology E F ≤ projTensorTopology E F ∧
      projTensorTopology E F ≤ epsTensorTopology E F := by sorry

end MasulloGRH
