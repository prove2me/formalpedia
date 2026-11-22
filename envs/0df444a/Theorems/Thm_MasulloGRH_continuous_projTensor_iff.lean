-- Prove2me | Theorems.Thm_MasulloGRH_continuous_projTensor_iff
-- name    : MasulloGRH.continuous_projTensor_iff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:20.804752+00:00
-- url     : https://prove2.me/theorems/77d83862-3966-4d16-9458-d3ac4966ea92
-- title:
--   Universal property of the projective tensor product: $T:E\otimes_\pi F\to G$ is continuous iff $(x,y)\mapsto T(x\otimes y)$ is continuous
-- statement:
--   **Universal property of the projective tensor product topology.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Hausdorff locally convex spaces, let $G$ be a locally convex space (not necessarily Hausdorff), and let $T:E\otimes F\to G$ be a linear map, with associated bilinear map $b(x,y)=T(x\otimes y)$. Then
--   $$T:E\otimes_\pi F\to G\ \text{ is continuous}\iff b:E\times F\to G\ \text{ is (jointly) continuous}.$$
--
--   Thus continuous linear maps $E\otimes_\pi F\to G$ correspond bijectively to continuous bilinear maps $E\times F\to G$; for $G=\mathbb C$ this identifies the continuous dual of $E\otimes_\pi F$ with the space $B(E,F)$ of continuous bilinear forms. This is the property by which the paper characterises $E\otimes_\pi F$, and the basic tool for constructing continuous maps out of projective tensor products (e.g. of Schwartz–Bruhat spaces).
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. `IsLocallyConvexTopology G _` says that the topology of $G$ is defined by a family of seminorms; $G$ may live in a different universe from $E$ and $F$ (which share one, as required by the platform definition).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 679, §C.2.3.2, the paragraph containing (C.2.3.14)

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem continuous_projTensor_iff (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F)
    (G : Type v) [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hG : IsLocallyConvexTopology G ‹TopologicalSpace G›) (T : E ⊗[ℂ] F →ₗ[ℂ] G) :
    @Continuous (E ⊗[ℂ] F) G (projTensorTopology E F) _ T ↔
      Continuous (fun p : E × F => T (p.1 ⊗ₜ[ℂ] p.2)) := by sorry

end MasulloGRH
