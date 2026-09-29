-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_finiteDimensional_fixingSubgroup_smul_eq
-- name    : ModularCurve.JZero.exists_finiteDimensional_fixingSubgroup_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/b7a0622d-59bc-5718-bcc7-a2b4b4f5f8b1
-- title:
--   Points of J₀(N) over ℚ̄ have open stabilisers
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $x$ be an element of `JZero N`, that is, of the degree-zero divisor class group $\mathrm{Pic}^0$ — the quotient of the group of degree-zero divisors of the field extension $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar N` by the subgroup of principal divisors lying in it — where `modularFunctionFieldBar N` is the base change to $\overline{\mathbb{Q}}$, inside the field of Laurent series over $\overline{\mathbb{Q}}$, of the full modular function field `modularFunctionFieldFull N` of level $N$ over $\mathbb{Q}$. The group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ acts on this group by a `DistribMulAction`. The assertion is that there exists an intermediate field $L_0$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ which is finite-dimensional over $\mathbb{Q}$ and such that every automorphism $\sigma$ in the fixing subgroup of $L_0$, i.e. every $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ restricting to the identity on $L_0$, satisfies $\sigma \bullet x = x$. In other words, each class $x$ is fixed by an open subgroup of the Galois group, so is defined over a number field.
--
--   This is the statement that the Galois action on the points of the modular Jacobian over $\overline{\mathbb{Q}}$ is smooth, i.e. that $J_0(N)(\overline{\mathbb{Q}})$ is the union of the groups of points rational over number fields, with stabilisers of points open. It is the finite-level input used downstream, for instance in the statements about the two-torsion and the invariants of the Galois action on `JZero N` ([`ModularCurve.JZero.exists_finiteDimensional_torsion_two_le_invariants`](thm.html#ModularCurve.JZero.exists_finiteDimensional_torsion_two_le_invariants), [`ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants`](thm.html#ModularCurve.JZero.finiteIndex_range_nsmul_two_invariants)) and in the analysis of places and their decomposition. The proof relies on the unconditional existence of principal divisors for `modularFunctionFieldBar N` and on the characterisation of membership in a valuation subring by nonnegativity of the order function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_finiteDimensional_fixingSubgroup_smul_eq.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.exists_finiteDimensional_fixingSubgroup_smul_eq (N : ℕ) [NeZero N] (x : JZero N) :
    ∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧ ∀ σ ∈ L₀.fixingSubgroup, σ • x = x := by sorry
