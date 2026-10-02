-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_continuity_principle_of_psh_convex
-- name    : LeblSCV.Pseudoconvex.continuity_principle_of_psh_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:39:41.503983+00:00
-- url     : https://prove2.me/theorems/8e18bd81-09a5-4d50-bea4-610bf566ce58
-- title:
--   Theorem 2.5.2 — Kontinuitätssatz (continuity principle, second version)
-- statement:
--   Suppose an open set $U \subset \mathbb{C}^n$ is convex with respect to the plurisubharmonic functions on $U$. Let $\{\Delta_\alpha\}$ be any collection of closed analytic discs $\Delta_\alpha \subset U$ such that $\bigcup_\alpha \partial\Delta_\alpha \subset\subset U$. Then
--   $$\bigcup_\alpha \Delta_\alpha \subset\subset U.$$
--
--   This is the implication (iii) $\Rightarrow$ (iv) of Theorem 2.5.6. It shows that discs whose boundaries stay in a compact part of $U$ cannot approach the boundary of $U$.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Convexity is `IsConvexWrt U {f | IsPlurisubharmonicOn f U}`, i.e. with respect to the `EReal`-valued plurisubharmonic functions defined on $U$. The conclusion is `SatisfiesContinuityPrinciple U`, in which $\Delta_\alpha = \varphi_\alpha(\mathbb{D})$ as in Definition 1.4.5.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 90, Theorem 2.5.2

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_IsConvexWrt
import Definitions.Def_LeblSCV_Pseudoconvex_SatisfiesContinuityPrinciple

namespace LeblSCV.Pseudoconvex

/-- Theorem 2.5.2 (Kontinuitätssatz, second version; Lebl, p. 90). If an open set `U ⊂ ℂⁿ` is
convex with respect to plurisubharmonic functions (on `U`), then for any collection of closed
analytic discs `Δ_α ⊂ U` with `⋃_α ∂Δ_α ⊂⊂ U` we have `⋃_α Δ_α ⊂⊂ U`. -/
theorem continuity_principle_of_psh_convex {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hU : IsOpen U) (hconv : IsConvexWrt U {f | IsPlurisubharmonicOn f U}) :
    SatisfiesContinuityPrinciple U := by sorry

end LeblSCV.Pseudoconvex
