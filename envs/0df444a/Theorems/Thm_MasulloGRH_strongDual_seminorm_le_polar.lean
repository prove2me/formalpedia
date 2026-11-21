-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_seminorm_le_polar
-- name    : MasulloGRH.strongDual_seminorm_le_polar
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:32.482995+00:00
-- url     : https://prove2.me/theorems/e0e5d2e4-d28e-4c00-9ad8-488374587f85
-- title:
--   Continuous seminorms on the strong dual are dominated by polar gauges of bounded sets
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ and let $E'_\beta$ be its strong dual (topology of uniform convergence on bounded subsets of $E$). Then every continuous seminorm $p$ on $E'_\beta$ is dominated by the gauge of the polar of a bounded set: there exist a (von Neumann) bounded set $B\subseteq E$ and a constant $C\ge 0$ such that for every $f\in E'$ and every $r\ge 0$,
--
--   $$\sup_{x\in B}|f(x)|\le r\quad\Longrightarrow\quad p(f)\le C\,r.$$
--
--   This is immediate from the definition of the strong topology: the sets $\{f : \sup_B |f|<\varepsilon\}$, $B$ bounded, form a basis of $0$-neighbourhoods, and $p$ is homogeneous.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.2.4 (nuclearity of the strong dual of a nuclear Fréchet space); cf. Schaefer, Topological Vector Spaces, III.7 and IV.9.6; Pietsch, Nuclear Locally Convex Spaces, 4.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_seminorm_le_polar (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (p : Seminorm ℂ (StrongDual ℂ E)) (hp : Continuous p) :
    ∃ (B : Set E) (C : ℝ), Bornology.IsVonNBounded ℂ B ∧ 0 ≤ C ∧
      ∀ (f : StrongDual ℂ E) (r : ℝ), 0 ≤ r → (∀ x ∈ B, ‖f x‖ ≤ r) → p f ≤ C * r := by sorry

end MasulloGRH
