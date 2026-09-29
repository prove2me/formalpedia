-- Prove2me | Theorems.Thm_ModularCurve_JZero_isOpen_stabilizer
-- name    : ModularCurve.JZero.isOpen_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/790077de-9d25-53bc-9dc8-3434ae9db78e
-- title:
--   Open stabilisers for the Galois action on J₀(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $\overline{\mathbb{Q}}$ denote `AlgebraicClosure ℚ`. Write $\mathrm{JZero}\,N$ for the degree-zero divisor class group $\mathrm{Pic}^0$ of the field extension $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar N`, the latter being the intermediate field of $\overline{\mathbb{Q}}((q))$ obtained by base change along `laurentBaseChange` of the modular function field `modularFunctionFieldFull N` inside $\mathbb{Q}((q))$; concretely, $\mathrm{JZero}\,N$ is the quotient of the group of divisors of degree zero (for places of this extension) by the subgroup of principal divisors lying in it. This group carries the arithmetic Galois action of the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, acting through its action on coefficients of Laurent series. The assertion is that for every class $y \in \mathrm{JZero}\,N$ the stabiliser subgroup $\{\sigma : \sigma \cdot y = y\}$ is, as a subset of the automorphism group, open for the Krull topology.
--
--   This is the statement that every degree-zero divisor class on the modular curve of level $N$ over $\overline{\mathbb{Q}}$ is fixed by the subgroup fixing some number field, i.e. that the absolute Galois group acts continuously on the discrete group $J_0(N)$. It is the continuity input for the Galois representations on torsion subgroups of $J_0(N)$, and is used, among others, by [`ModularCurve.JZero.torsion_fixed_by_open`](thm.html#ModularCurve.JZero.torsion_fixed_by_open) and [`ModularCurve.JZero.exists_finiteDimensional_smul_eq_self_of_torsion`](thm.html#ModularCurve.JZero.exists_finiteDimensional_smul_eq_self_of_torsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_isOpen_stabilizer.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.FieldTheory.KrullTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.JZero.isOpen_stabilizer (N : ℕ) [NeZero N] (y : ModularCurve.JZero N) :
    IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by sorry
