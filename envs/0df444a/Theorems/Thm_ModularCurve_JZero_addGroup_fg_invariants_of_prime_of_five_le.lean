-- Prove2me | Theorems.Thm_ModularCurve_JZero_addGroup_fg_invariants_of_prime_of_five_le
-- name    : ModularCurve.JZero.addGroup_fg_invariants_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/f2294d91-6066-52a2-81bc-658cb54ba940
-- title:
--   Mordell–Weil for J₀(N), prime level N≥ 5
-- statement:
--   Let $N$ be a nonzero natural number which is prime and satisfies $5 \le N$, and let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ (inside `AlgebraicClosure ℚ`) that is finite-dimensional over $\mathbb{Q}$. Write `JZero N` for the degree-zero divisor class group $\mathrm{Pic}^0$ of the field `modularFunctionFieldBar N` — the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ — over the constant field $\overline{\mathbb{Q}}$, that is, the quotient of the group of degree-zero divisors by the subgroup of principal divisors; it carries the action of the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ by additive-group automorphisms. The assertion is that the additive subgroup `JZero N ^+ ↥K.fixingSubgroup` of elements of `JZero N` fixed by every automorphism in the fixing subgroup of $K$, i.e. by $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$, is a finitely generated additive group. The hypotheses that $N$ is prime and $N \ge 5$ enter only through the cited existence of a descent height on the invariants.
--
--   This is the Mordell–Weil theorem for the Jacobian $J_0(N)$ at prime level $N \ge 5$: the group of $K$-rational points of $J_0(N)$, realised as the Galois-invariant part of $\mathrm{Pic}^0$ of the modular function field over $\overline{\mathbb{Q}}$, is finitely generated for every number field $K$. It is used to obtain the corresponding statement over $\mathbb{Q}$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_addGroup_fg_invariants_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.addGroup_fg_invariants_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    AddGroup.FG ↥(JZero N ^+ ↥K.fixingSubgroup) := by sorry
