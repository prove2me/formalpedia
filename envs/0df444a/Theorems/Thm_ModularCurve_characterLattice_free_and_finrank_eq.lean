-- Prove2me | Theorems.Thm_ModularCurve_characterLattice_free_and_finrank_eq
-- name    : ModularCurve.characterLattice_free_and_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/953fe11c-177f-5b9c-9e51-0dcf5ab06474
-- title:
--   The degree-zero lattice ℤ[S]⁰ is free of rank |S|-1
-- statement:
--   Let $S$ be a finite type. Write $\mathrm{degreeOn}\,S \colon (S \to \mathbb Z) \to \mathbb Z$ for the $\mathbb Z$-linear map given by the sum $\sum_{x : S} \mathrm{pr}_x$ of the coordinate projections, i.e. the map sending a function $f$ to $\sum_{x} f(x)$, and let $\mathrm{characterLattice}\,S$ be its kernel, the submodule of degree-zero elements of $\mathbb Z^S$. The theorem asserts two things about this submodule: first, that it is a free $\mathbb Z$-module, and second, that its rank over $\mathbb Z$ equals $\mathrm{card}(S) - 1$, the subtraction being natural-number subtraction, so that for $S$ empty the asserted rank is $0$. No hypotheses beyond the finiteness of $S$ are imposed; in particular $S$ is not assumed non-empty, and the $S = \varnothing$ case is covered by the truncated subtraction.
--
--   This is the standard statement that the degree-zero part of the free module $\mathbb Z[S]$ on a finite set is free of rank $|S| - 1$; in the component-group computations it supplies, for a finite set of supersingular points or of components, the free $\mathbb Z$-module structure and rank of the character lattice. It is used in the analysis of the Néron model of a Jacobian at a prime of multiplicative reduction, where the toric and finite parts of the points are compared via the character lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_characterLattice_free_and_finrank_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.characterLattice_free_and_finrank_eq (S : Type*) [Fintype S] :
    Module.Free ℤ (ModularCurve.characterLattice S) ∧
      Module.finrank ℤ (ModularCurve.characterLattice S) = Fintype.card S - 1 := by sorry
