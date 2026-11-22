-- Prove2me | Theorems.Thm_MasulloGRH_indTensor_isHLCS
-- name    : MasulloGRH.indTensor_isHLCS
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:26.011811+00:00
-- url     : https://prove2.me/theorems/9511d9cd-dc8b-43ec-bfb3-19b588b1fcd1
-- title:
--   The inductive tensor product $E\otimes_\iota F$ of Hausdorff locally convex spaces is Hausdorff locally convex
-- statement:
--   **The inductive tensor product is a Hausdorff locally convex space.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Hausdorff locally convex spaces. Then $E\otimes_\iota F$ is a Hausdorff locally convex space.
--
--   With the Hausdorff property there is a good notion of completion of $E\otimes_\iota F$, the completed inductive tensor product $E\,\overline\otimes\,F$ of (C.2.3.23), which is the tensor product used throughout the paper.
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. The conclusion is `IsHLCS` for the topology `indTensorTopology E F` on `E ⊗[ℂ] F`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 682, §C.2.3.4, the paragraph between (C.2.3.22) and (C.2.3.23); classical reference: A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Memoirs of the AMS No. 16, Ch. I, §3, No. 1, Prop. 13, p. 73

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem indTensor_isHLCS (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    @IsHLCS (E ⊗[ℂ] F) _ _ (indTensorTopology E F) := by sorry

end MasulloGRH
