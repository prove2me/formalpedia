-- Prove2me | Theorems.Thm_MasulloGRH_continuous_indTensor_iff
-- name    : MasulloGRH.continuous_indTensor_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:19.362779+00:00
-- url     : https://prove2.me/theorems/f2a0c360-366f-463b-88db-12282d956c5a
-- title:
--   Universal property of the inductive tensor product: $T:E\otimes_\iota F\to G$ is continuous iff $(x,y)\mapsto T(x\otimes y)$ is separately continuous
-- statement:
--   **Universal property of the inductive tensor product topology.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Hausdorff locally convex spaces, let $G$ be a locally convex space, and let $T:E\otimes F\to G$ be a linear map, with associated bilinear map $b(x,y)=T(x\otimes y)$. Then
--   $$T:E\otimes_\iota F\to G\ \text{ is continuous}\iff b\ \text{ is separately continuous},$$
--   i.e. iff $y\mapsto T(x\otimes y)$ is continuous on $F$ for every $x\in E$ and $x\mapsto T(x\otimes y)$ is continuous on $E$ for every $y\in F$.
--
--   Thus continuous linear maps $E\otimes_\iota F\to G$ correspond bijectively to separately continuous bilinear maps $E\times F\to G$. The inductive tensor product (Grothendieck) is the tensor product that commutes with locally convex inductive limits, and is the one used throughout the paper for spaces of Schwartz–Bruhat functions on products.
--
--   **Deviation from the source.** On p. 682 the topology of $E\otimes_\iota F$ is described as the finest locally convex topology on $E\otimes F$ for which every separately continuous bilinear map $E\times F\to G$ into a Hausdorff locally convex space $G$ induces a continuous linear map $E\otimes F\to G$. Read literally, this is the finest locally convex topology on $E\otimes F$ (for which every linear map into a locally convex space is continuous), which in general is strictly finer than the inductive topology. The intended definition, used here, is the finest locally convex topology for which $\otimes:E\times F\to E\otimes F$ is separately continuous; it is the topology characterised by the universal property above.
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. $G$ may live in a different universe from $E$, $F$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 682, §C.2.3.4, the paragraph before (C.2.3.22); classical reference: A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Memoirs of the AMS No. 16, Ch. I, §3, No. 1, Prop. 13, p. 73 and Def. 3, p. 74; H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, p. 96

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem continuous_indTensor_iff (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F)
    (G : Type v) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hG : IsLocallyConvexTopology G ‹TopologicalSpace G›) (T : E ⊗[ℂ] F →ₗ[ℂ] G) :
    @Continuous (E ⊗[ℂ] F) G (indTensorTopology E F) _ T ↔
      (∀ x : E, Continuous (fun y : F => T (x ⊗ₜ[ℂ] y))) ∧
        (∀ y : F, Continuous (fun x : E => T (x ⊗ₜ[ℂ] y))) := by sorry

end MasulloGRH
