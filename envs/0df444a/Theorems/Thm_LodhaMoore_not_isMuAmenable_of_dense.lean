-- Prove2me | Theorems.Thm_LodhaMoore_not_isMuAmenable_of_dense
-- name    : LodhaMoore.not_isMuAmenable_of_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T22:40:56.07229+00:00
-- url     : https://prove2.me/theorems/ae6d0345-a254-4d49-a6d0-b6342fa93483
-- title:
--   Theorem 2.2 (external, Carrière–Ghys) — a countable dense subgroup of PSL₂(ℝ) has a non-μ-amenable orbit relation
-- statement:
--   Let $\Gamma$ be a countable dense subgroup of $\mathrm{PSL}_2(\mathbb R)$ (`Matrix.ProjectiveSpecialLinearGroup`, with the quotient topology). Then the orbit equivalence relation of its action on the projective line ($x \sim y$ when some matrix whose class lies in $\Gamma$ maps $x$ to $y$ by its Möbius transformation, `Monod.mob`) is not $\mu$-amenable (`IsMuAmenable`) for Lebesgue measure (`Monod.volP1`).
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, Theorem 2.2

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective

namespace LodhaMoore

theorem not_isMuAmenable_of_dense
    (Γ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ))) [Countable Γ]
    (hΓ : Dense (Γ : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)))) :
    ¬ IsMuAmenable Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ Γ ∧ Monod.mob A p.1 = p.2} := by
  sorry

end LodhaMoore
