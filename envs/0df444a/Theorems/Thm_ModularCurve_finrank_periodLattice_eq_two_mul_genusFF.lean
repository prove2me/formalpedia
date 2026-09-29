-- Prove2me | Theorems.Thm_ModularCurve_finrank_periodLattice_eq_two_mul_genusFF
-- name    : ModularCurve.finrank_periodLattice_eq_two_mul_genusFF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/c795dfdc-cc1f-5df7-b701-474f3c74168f
-- title:
--   Rank of the period lattice equals twice the genus
-- statement:
--   Let $N$ be a nonzero natural number. On one side stands `periodLattice N`, the $\mathbb{Z}$-submodule of the $\mathbb{C}$-linear dual of $\mathrm{CuspForm}(\Gamma_0(N),2)$ spanned by the range of the map `period N`, which sends $\gamma \in \Gamma_0(N)$ to the functional `periodAlong N` taken from the point $i$ of the upper half-plane to its translate $\gamma \cdot i$ under the image of $\gamma$ in $\mathrm{SL}(2,\mathbb{Z})$. On the other side stands `genusFF` of the field extension $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar N`, that is, the $\overline{\mathbb{Q}}$-dimension of the repartition cohomology group $H^1$ of the zero divisor, where a divisor is a finitely supported $\mathbb{Z}$-valued function on the places of the extension; here `modularFunctionFieldBar N` is `laurentBaseChange` over $\overline{\mathbb{Q}}$ of `modularFunctionFieldFull N`, i.e. the intermediate field of $\overline{\mathbb{Q}}$-Laurent series generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the subfield of $\mathbb{Q}$-Laurent series obtained by adjoining to $\mathbb{Q}$ the family `divisorExpansions N`. The assertion is that the $\mathbb{Z}$-rank of `periodLattice N` equals $2$ times this genus.
--
--   This is the comparison of the topological and the algebraic genus of $X_0(N)$: the period lattice of weight-two cusp forms of level $N$ has rank $2g$, where $g$ is the Riemann–Roch genus of the modular function field over $\overline{\mathbb{Q}}$. It is used downstream in the study of the Jacobian $J_0(N)$, in particular in the finiteness and cardinality statements about its torsion and its reduction used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_periodLattice_eq_two_mul_genusFF.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.finrank_periodLattice_eq_two_mul_genusFF (N : ℕ) [NeZero N] :
    Module.finrank ℤ (periodLattice N) =
      2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := by sorry
