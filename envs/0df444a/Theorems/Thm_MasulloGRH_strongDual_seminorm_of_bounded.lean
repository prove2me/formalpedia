-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_seminorm_of_bounded
-- name    : MasulloGRH.strongDual_seminorm_of_bounded
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:30:45.089187+00:00
-- url     : https://prove2.me/theorems/073742aa-ac06-412f-803b-22d48fe5f33c
-- title:
--   Bounded sets give continuous seminorms on the strong dual
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ and let $B\subseteq E$ be a (von Neumann) bounded set. Then there is a continuous seminorm $p$ on the strong dual $E'_\beta$ such that
--
--   $$|f(x)|\le p(f)\qquad\text{for all } f\in E',\ x\in B.$$
--
--   Indeed one may take $p_B(f)=\sup_{x\in B}|f(x)|$, which is finite because every continuous linear functional is bounded on bounded sets, and which is continuous for the strong topology (the topology of uniform convergence on bounded subsets of $E$) since its unit ball is the polar $B^\circ$, a basic $0$-neighbourhood of $E'_\beta$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.1.4 and §C.2.4; cf. H. H. Schaefer, Topological Vector Spaces, Ch. IV §5 and III.7, and A. Pietsch, Nuclear Locally Convex Spaces, 4.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_seminorm_of_bounded (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ p : Seminorm ℂ (StrongDual ℂ E), Continuous p ∧
      ∀ (f : StrongDual ℂ E), ∀ x ∈ B, ‖f x‖ ≤ p f := by sorry

end MasulloGRH
