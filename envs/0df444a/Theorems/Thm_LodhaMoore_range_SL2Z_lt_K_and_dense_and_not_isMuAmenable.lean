-- Prove2me | Theorems.Thm_LodhaMoore_range_SL2Z_lt_K_and_dense_and_not_isMuAmenable
-- name    : LodhaMoore.range_SL2Z_lt_K_and_dense_and_not_isMuAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:17:00.65712+00:00
-- url     : https://prove2.me/theorems/ffa49ab4-3323-4b01-ac35-563d104797e6
-- title:
--   §2 — K properly contains PSL₂(ℤ), is dense, and its orbit relation is not μ-amenable
-- statement:
--   The image of $\mathrm{SL}_2(\mathbb Z)$ in $\mathrm{PSL}_2(\mathbb R)$, that is $\mathrm{PSL}_2(\mathbb Z)$, is a proper subgroup of $K$; $K$ is dense in $\mathrm{PSL}_2(\mathbb R)$; and the orbit equivalence relation of the action of $K$ on the projective line is not $\mu$-amenable (`IsMuAmenable`) for Lebesgue measure.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, §2

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective

namespace LodhaMoore

theorem range_SL2Z_lt_K_and_dense_and_not_isMuAmenable :
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (⊤ : Subring ℝ))).range.map
      (QuotientGroup.mk' _ : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) < K ∧
    Dense (K : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ))) ∧
    ¬ IsMuAmenable Monod.volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ A : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
        (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (⊤ : Subring ℝ)) ∈ K ∧ Monod.mob A p.1 = p.2} := by
  sorry

end LodhaMoore
