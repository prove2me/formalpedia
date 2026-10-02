-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_cartan_thullen
-- name    : LeblSCV.Pseudoconvex.cartan_thullen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:14:51.380601+00:00
-- url     : https://prove2.me/theorems/7ca1e88c-6ff1-4519-87b8-af81cd876586
-- title:
--   Theorem 2.6.3 (Cartan–Thullen) — domains of holomorphy are the holomorphically convex domains
-- statement:
--   Let $U \subsetneq \mathbb{C}^n$ be a domain. The following are equivalent:
--
--   (i) $U$ is a domain of holomorphy;
--
--   (ii) for all $K \subset\subset U$,
--   $$\operatorname{dist}(K, \partial U) = \operatorname{dist}(\widehat{K}_U, \partial U);$$
--
--   (iii) $U$ is holomorphically convex.
--
--   The theorem replaces the extrinsic notion of a domain of holomorphy by the intrinsic notion of holomorphic convexity.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. For $A \subset \mathbb{C}^n$, $\operatorname{dist}(A, \partial U) = \inf_{x \in A} \inf_{w \in \partial U} \|x - w\|$ is computed in $[0, \infty]$ with `Metric.infEDist`, so the infimum over a set is genuine rather than a junk value. A domain is `IsOpen U ∧ IsConnected U`, and $U \subsetneq \mathbb{C}^n$ is `U ≠ Set.univ`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 100, Theorem 2.6.3

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsDomainOfHolomorphy
import Definitions.Def_LeblSCV_Pseudoconvex_holomorphicHull
import Definitions.Def_LeblSCV_Pseudoconvex_IsHolomorphicallyConvex
import Definitions.Def_LeblSCV_Pseudoconvex_IsRelCompactIn

namespace LeblSCV.Pseudoconvex

/-- Theorem 2.6.3 (Cartan–Thullen; Lebl, p. 100). Let `U ⊊ ℂⁿ` be a domain. The following are
equivalent:
(i) `U` is a domain of holomorphy;
(ii) for all `K ⊂⊂ U`, `dist(K, ∂U) = dist(K̂_U, ∂U)`;
(iii) `U` is holomorphically convex.
`dist(A, ∂U) = inf_{x ∈ A} inf_{w ∈ ∂U} ‖x − w‖` is the Euclidean distance, computed in
`[0, ∞]` (`Metric.infEDist`) so that the infimum over a set is genuine. -/
theorem cartan_thullen {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ) :
    List.TFAE
      [IsDomainOfHolomorphy U,
       ∀ K : Set (EuclideanSpace ℂ (Fin n)), IsRelCompactIn K U →
         (⨅ x ∈ K, Metric.infEDist x (frontier U)) =
           ⨅ x ∈ holomorphicHull U K, Metric.infEDist x (frontier U),
       IsHolomorphicallyConvex U] := by sorry

end LeblSCV.Pseudoconvex
