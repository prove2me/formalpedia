-- Prove2me | Theorems.Thm_MasulloGRH_nuclearFrechet_bounded_nuclear_domination
-- name    : MasulloGRH.nuclearFrechet_bounded_nuclear_domination
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:35.141584+00:00
-- url     : https://prove2.me/theorems/6ef4d490-8ca3-46b4-8cbf-9abeb89cdab9
-- title:
--   Bounded sets of a nuclear Fréchet space are nuclearly dominated
-- statement:
--   Let $E$ be a nuclear Fréchet space over $\mathbb C$ (nuclear in Grothendieck's sense, Definition C.2.4.1) and let $B\subseteq E$ be bounded. Then there exist a bounded sequence $(y_n)_{n\ge0}$ in $E$ and reals $c_n\ge 0$ with $\sum_n c_n<\infty$ such that for every continuous linear functional $f\in E'$ and every $x\in B$,
--
--   $$|f(x)|\le\sum_{n=0}^{\infty}c_n\,|f(y_n)|.$$
--
--   This is the dual form of the classical fact that in a (quasi-)complete nuclear space every bounded closed absolutely convex set $B$ is contained in a bounded absolutely convex $D$ such that the canonical map $E_B\to E_D$ is nuclear, $x\mapsto\sum_n c_n\varphi_n(x)y_n$ with $\|\varphi_n\|_{E_B'}\le1$, $y_n\in D$ (Pietsch 4.4; Schaefer III.7).
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.2.4 (nuclearity of the strong dual of a nuclear Fréchet space); cf. Schaefer, Topological Vector Spaces, III.7 and IV.9.6; Pietsch, Nuclear Locally Convex Spaces, 4.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclearFrechet_bounded_nuclear_domination (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → E) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
      Summable c ∧ ∀ (f : StrongDual ℂ E), ∀ x ∈ B, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by sorry

end MasulloGRH
