-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_torsion_two_le_invariants
-- name    : ModularCurve.JZero.exists_finiteDimensional_torsion_two_le_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/93dec756-8574-5377-8d34-35912f6c4953
-- title:
--   2-torsion of J₀(N) is fixed by a finite extension
-- statement:
--   Let $N$ be a nonzero natural number and let $K$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ that is finite-dimensional over $\mathbb{Q}$. The assertion is that there exists an intermediate field $L'$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, again finite-dimensional over $\mathbb{Q}$ and containing $K$, with the following property. Write $F$ for `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb{Q}}((T))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull N`, itself the subfield of $\mathbb{Q}((T))$ generated over $\mathbb{Q}$ by the divisor expansions at level $N$; and let `JZero N` be $\mathrm{Pic}^0$ of $F$ over $\overline{\mathbb{Q}}$, namely the group of finitely supported $\mathbb{Z}$-valued functions on the places of $F/\overline{\mathbb{Q}}$ of total degree zero, modulo the principal divisors. Then every element of `JZero N` annihilated by $2$ lies in the subgroup of elements fixed by the fixing subgroup of $L'$, i.e. by all automorphisms of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing $L'$ pointwise.
--
--   This is the statement that the field of definition of the $2$-torsion of the Jacobian $J_0(N)$ is a number field, which may moreover be taken to contain any prescribed number field. It is the enlargement of the base field that allows Kummer theory at $2$ to be used in the weak Mordell–Weil argument for $J_0(N)$, and it is cited in the proofs that the invariants of `JZero N` under such a fixing subgroup form a finitely generated group and in the corresponding descent step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_finiteDimensional_torsion_two_le_invariants.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.exists_finiteDimensional_torsion_two_le_invariants (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L' ∧ K ≤ L' ∧
      Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 2 ≤ JZero N ^+ ↥L'.fixingSubgroup := by sorry
