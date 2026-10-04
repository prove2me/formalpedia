-- Prove2me | Theorems.Thm_LodhaMoore_orbit_G0_eq_orbit_K_of_irrational
-- name    : LodhaMoore.orbit_G0_eq_orbit_K_of_irrational
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T06:14:42.413629+00:00
-- url     : https://prove2.me/theorems/827ca32b-ca56-4f5f-ace4-8df9812a59d7
-- title:
--   §2 — every irrational point has the same orbit under G₀ as under K
-- statement:
--   For every irrational $t$, the $G_0$-orbit of $t$ equals its $K$-orbit: a point of the projective line is the image of $t$ under some element of $G_0$ if and only if it is the image of $t$ under some element of $K$ (a matrix whose class lies in $K$, by its Möbius action).
--
--   **Formalization Note.** The quoted sentence says what this equality is for. By Theorem 2.1 ($G_0$ is countable and acts by homeomorphisms of the projective line), were $G_0$ amenable its orbit relation would be $\mu$-amenable for Lebesgue measure; the rationals and $\infty$ form a countable set, invariant under both groups and hence null, so the orbit relation of $K$ would be $\mu$-amenable too, contradicting `range_SL2Z_lt_K_and_dense_and_not_isMuAmenable`. That reduction is the route to the goal, not part of this statement.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, §2

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective

namespace LodhaMoore

theorem orbit_G0_eq_orbit_K_of_irrational (t : ℝ) (ht : Irrational t) :
    {y : OnePoint ℝ | ∃ g ∈ G0, g (t : OnePoint ℝ) = y} =
      {y : OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ K ∧
          Monod.mob A (t : OnePoint ℝ) = y} := by
  sorry

end LodhaMoore
