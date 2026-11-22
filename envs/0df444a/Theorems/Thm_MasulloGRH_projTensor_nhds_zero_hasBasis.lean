-- Prove2me | Theorems.Thm_MasulloGRH_projTensor_nhds_zero_hasBasis
-- name    : MasulloGRH.projTensor_nhds_zero_hasBasis
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:18.052798+00:00
-- url     : https://prove2.me/theorems/69ee58b6-59fc-4e30-bc4e-aab89c04c360
-- title:
--   Neighbourhood base of $0$ in $E\otimes_\pi F$: the convex circled hulls of $U\otimes V$
-- statement:
--   **A fundamental system of neighbourhoods of $0$ for the projective tensor product topology.**
--
--   Throughout, vector spaces are over $\mathbb C$ and a topology on a vector space is *locally convex* if it is defined by a family of seminorms. For topological vector spaces $E$, $F$:
--
--   - the **projective topology** $\pi$ on the algebraic tensor product $E\otimes F$ is the finest locally convex topology for which the canonical bilinear map $\otimes:E\times F\to E\otimes F$ is continuous; $E\otimes_\pi F$ denotes $E\otimes F$ with this topology;
--   - the **inductive topology** $\iota$ is the finest locally convex topology for which $\otimes$ is separately continuous; $E\otimes_\iota F$;
--   - the **injective topology** $\varepsilon$ is the topology of uniform convergence on the products $A\times B$ of equicontinuous subsets $A\subseteq E'$, $B\subseteq F'$, a tensor $u$ being regarded as the function $(x',y')\mapsto(x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$.
--
--   Let $E$, $F$ be Hausdorff locally convex spaces. For subsets $U\subseteq E$, $V\subseteq F$ put
--   $$U\otimes V=\{u\otimes v:\ u\in U,\ v\in V\}\subseteq E\otimes F,$$
--   and let $\Gamma(U\otimes V)$ be its convex circled hull (the smallest convex, balanced subset of $E\otimes F$ containing it). Then the sets
--   $$\Gamma(U\otimes V),\qquad U\ \text{a neighbourhood of }0\text{ in }E,\quad V\ \text{a neighbourhood of }0\text{ in }F,$$
--   form a fundamental system of neighbourhoods of $0$ in $E\otimes_\pi F$: each of them is a neighbourhood of $0$, and every neighbourhood of $0$ in $E\otimes_\pi F$ contains one of them.
--
--   Since $\Gamma(U\otimes V)$ is increasing in $U$ and $V$, it is equivalent to let $U$ and $V$ run through fundamental systems of neighbourhoods of $0$, as in (C.2.3.15). This concrete description is what makes the projective topology computable (cross seminorms $p\otimes q$, behaviour under quotient maps, associativity, Grothendieck's series representation).
--
--   **Formalization Note.** The topologies are the platform definitions `projTensorTopology`, `indTensorTopology`, `epsTensorTopology` of `Def_MasulloGRH_LocallyConvex` on Mathlib's algebraic tensor product `E ⊗[ℂ] F`; `IsHLCS` means that the topology is defined by a family of seminorms and is Hausdorff. The conclusion is `Filter.HasBasis` for the neighbourhood filter of $0$ in `projTensorTopology E F`, indexed by pairs $(U,V)$ of neighbourhoods of $0$; the convex circled hull is Mathlib's `absConvexHull ℂ` (balanced over $\mathbb C$ and convex, with the order `ComplexOrder` on $\mathbb C$, for which convexity is real convexity).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 679, §C.2.3.2, (C.2.3.15); classical reference: F. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 43; H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, pp. 93–94

import Definitions.Def_MasulloGRH_LocallyConvex

open TensorProduct Topology Filter
open scoped ComplexOrder
set_option autoImplicit false
universe u v

namespace MasulloGRH

theorem projTensor_nhds_zero_hasBasis (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    (@nhds (E ⊗[ℂ] F) (projTensorTopology E F) 0).HasBasis
      (fun UV : Set E × Set F => UV.1 ∈ 𝓝 (0 : E) ∧ UV.2 ∈ 𝓝 (0 : F))
      (fun UV => absConvexHull ℂ (Set.image2 (fun x y => x ⊗ₜ[ℂ] y) UV.1 UV.2)) := by sorry

end MasulloGRH
