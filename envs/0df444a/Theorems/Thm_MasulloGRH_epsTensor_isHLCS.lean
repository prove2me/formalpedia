-- Prove2me | Theorems.Thm_MasulloGRH_epsTensor_isHLCS
-- name    : MasulloGRH.epsTensor_isHLCS
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:31.397812+00:00
-- url     : https://prove2.me/theorems/781bf7a9-3db7-46db-8fc2-6fb0c5c71d6e
-- title:
--   The injective tensor product $E\otimes_\varepsilon F$ of Hausdorff locally convex spaces is Hausdorff locally convex
-- statement:
--   **The injective tensor product is a Hausdorff locally convex space.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Hausdorff locally convex spaces. Then $E\otimes_\varepsilon F$ is a Hausdorff locally convex space: its topology is defined by the seminorms
--   $$\varepsilon_{A,B}(u)=\sup\{|(x'\otimes y')(u)|:\ x'\in A,\ y'\in B\},$$
--   for $A\subseteq E'$, $B\subseteq F'$ equicontinuous, and it separates points (because $E'$ and $F'$ separate the points of $E$ and $F$).
--
--   This is the basic well-definedness fact for the $\varepsilon$-tensor product (it is needed to form the completion $E\widehat\otimes_\varepsilon F$) and the counterpart of the corresponding statement for $E\otimes_\pi F$.
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. The conclusion is `IsHLCS` for the topology `epsTensorTopology E F` on `E ⊗[ℂ] F`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 676, §C.2.3.1, after (C.2.3.4); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, Cor. to 3.2 (applied to $\mathscr L_\varepsilon(E'_\tau,F)$); F. Trèves, Topological Vector Spaces, Distributions and Kernels, Def. 43.1

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem epsTensor_isHLCS (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    @IsHLCS (E ⊗[ℂ] F) _ _ (epsTensorTopology E F) := by sorry

end MasulloGRH
