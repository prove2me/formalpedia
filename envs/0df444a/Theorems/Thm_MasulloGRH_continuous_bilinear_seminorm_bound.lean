-- Prove2me | Theorems.Thm_MasulloGRH_continuous_bilinear_seminorm_bound
-- name    : MasulloGRH.continuous_bilinear_seminorm_bound
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:48.816103+00:00
-- url     : https://prove2.me/theorems/965c9acd-29bd-4157-bb7a-6c206255211d
-- title:
--   A continuous bilinear form is bounded by a product of continuous seminorms
-- statement:
--   Let $E$ and $F$ be complex vector spaces whose topologies are locally convex (each defined by a family of seminorms), and let $B\colon E\times F\to\mathbb C$ be a bilinear form which is (jointly) continuous on $E\times F$. Then there are continuous seminorms $p$ on $E$ and $r$ on $F$ such that
--
--   $$|B(x,y)|\le p(x)\,r(y)\qquad\text{for all }x\in E,\ y\in F.$$
--
--   This is the standard reformulation of joint continuity of bilinear forms on locally convex spaces in terms of seminorms; it is the first step of the proof of the Schwartz kernel theorem.
--
--   **Formalization Note** Local convexity is the predicate `IsLocallyConvexTopology` of the definition file; continuity of $B$ is continuity of $(x,y)\mapsto B(x,y)$ for the product topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.2.4.18 (Schwartz kernel theorem) and its proof; cf. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 50 (Theorem 50.1 and Proposition 50.5)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem continuous_bilinear_seminorm_bound (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›)
    (hF : IsLocallyConvexTopology F ‹TopologicalSpace F›)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : Continuous (fun p : E × F => B p.1 p.2)) :
    ∃ (p : Seminorm ℂ E) (r : Seminorm ℂ F), Continuous p ∧ Continuous r ∧
      ∀ x y, ‖B x y‖ ≤ p x * r y := by sorry

end MasulloGRH
