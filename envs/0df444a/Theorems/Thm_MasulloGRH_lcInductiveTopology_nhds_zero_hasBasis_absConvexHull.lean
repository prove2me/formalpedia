-- Prove2me | Theorems.Thm_MasulloGRH_lcInductiveTopology_nhds_zero_hasBasis_absConvexHull
-- name    : MasulloGRH.lcInductiveTopology_nhds_zero_hasBasis_absConvexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:52.436882+00:00
-- url     : https://prove2.me/theorems/31106026-d46d-4a9b-a21f-326de2f17b02
-- title:
--   A base of $0$-neighbourhoods of the locally convex inductive topology: absolutely convex hulls of unions of images of stage neighbourhoods, cf. (C.1.5.1)
-- statement:
--   **Neighbourhoods of $0$ for the locally convex inductive topology.** Let $E$ be a complex vector space, $(E_\alpha)_{\alpha\in A}$ a non-empty family of topological vector spaces over $\mathbb C$ and $f_\alpha\colon E_\alpha\to E$ linear maps whose images span $E$:
--   $$E=\sum_{\alpha\in A}f_\alpha(E_\alpha).$$
--   Let $\tau$ be the locally convex inductive topology on $E$, the finest locally convex topology for which all $f_\alpha$ are continuous. For a family $U=(U_\alpha)_{\alpha\in A}$ with $U_\alpha$ a neighbourhood of $0$ in $E_\alpha$, let
--   $$\Gamma(U)=\Bigl\{\sum_{i=1}^{n}\lambda_i\,y_i:\ n\ge 1,\ y_i\in\bigcup_{\alpha}f_\alpha(U_\alpha),\ \lambda_i\in\mathbb C,\ \sum_{i=1}^n|\lambda_i|\le 1\Bigr\}$$
--   be the absolutely convex (convex circled) hull of $\bigcup_\alpha f_\alpha(U_\alpha)$. Then the sets $\Gamma(U)$, as $U$ ranges over all such families, form a base of neighbourhoods of $0$ for $\tau$.
--
--   For the algebraic direct sum $E=\bigoplus_\alpha E_\alpha$ of locally convex spaces with the canonical injections, and convex circled $U_\alpha$, the set $\Gamma(U)$ is
--   $$\Bigl\{\sum_\alpha\lambda_\alpha x_\alpha:\ x_\alpha\in U_\alpha,\ \sum_\alpha|\lambda_\alpha|\le 1\Bigr\},$$
--   which is the base of $0$-neighbourhoods (C.1.5.1) by which the source describes the locally convex direct sum topology; the source uses it in the proof of Proposition C.1.5.1 and, through quotients, for general inductive limits.
--
--   **Formalization Note.** $\tau$ is `sInf` of the set of locally convex topologies (`MasulloGRH.IsLocallyConvexTopology`) making all `f a` continuous. The absolutely convex hull of a set $S$ is written `convexHull ℝ (balancedHull ℂ S)` (the convex hull of the circled hull). The spanning hypothesis is `⨆ a, LinearMap.range (f a) = ⊤`; it is necessary, since the hulls lie in the span of the images. The index type is assumed non-empty (otherwise the union is empty and $E=0$). The neighbourhoods $U_\alpha$ are arbitrary, not necessarily convex or circled.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 663, §C.1.5, equation (C.1.5.1) and the preceding paragraph; classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, p. 54 (as cited by the paper on p. 662)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem lcInductiveTopology_nhds_zero_hasBasis_absConvexHull (E : Type*) [AddCommGroup E]
    [Module ℂ E] {ι : Type*} [Nonempty ι] (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E)
    (hspan : ⨆ a, LinearMap.range (f a) = ⊤) :
    (@nhds E (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)})
        0).HasBasis
      (fun U : ∀ a, Set (X a) => ∀ a, U a ∈ 𝓝 (0 : X a))
      (fun U => convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) := by sorry

end MasulloGRH
