-- Prove2me | Theorems.Thm_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion
-- name    : ModularCurve.JOne.exists_finiteDimensional_smul_eq_self_of_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/54beaa82-a0e8-5381-9cb0-0652ca84c5cd
-- title:
--   Torsion of J₁(M) fixed by a number field's stabiliser
-- statement:
--   Let $M$ be a natural number with $M \neq 0$ and let $n$ be a natural number with $n > 0$. Write $\bar{\mathbb Q} =$ `AlgebraicClosure ℚ`, let `x1FunctionFieldBar M` be the base change along `laurentBaseChange` of the function field `x1FunctionField M` of $X_1(M)$ to the field of Laurent series over $\bar{\mathbb Q}$, and let [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) be $\mathrm{Pic}^0$ of this field over $\bar{\mathbb Q}$, that is, the quotient of the group of degree-zero divisors by the subgroup of principal divisors, carrying the natural action of the group of $\mathbb Q$-algebra automorphisms of $\bar{\mathbb Q}$ (coefficientwise on Laurent series). The assertion is that there exists an intermediate field $L$ between $\mathbb Q$ and $\bar{\mathbb Q}$ which is finite-dimensional over $\mathbb Q$, such that for every $\mathbb Q$-algebra automorphism $\sigma$ of $\bar{\mathbb Q}$ with $\sigma x = x$ for all $x \in L$, and for every $P \in$ [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) with $(n : \mathbb Z) \cdot P = 0$, one has $\sigma \cdot P = P$. Thus the $n$-torsion of $J_1(M)$ is fixed pointwise by the subgroup of $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ fixing some number field.
--
--   This is the statement that the $n$-torsion of the Jacobian of $X_1(M)$ is defined over a number field, equivalently that the Galois action on each torsion subgroup becomes trivial on an open subgroup of $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$. It supplies the continuity input for the adic Galois representations attached to modular curves, and is used in the construction of those representations together with their Frobenius and inertia relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.JOne.exists_finiteDimensional_smul_eq_self_of_torsion (M : ℕ) [NeZero M]
    (n : ℕ) (hn : 0 < n) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ P : ModularCurve.JOne M, (n : ℤ) • P = 0 → σ • P = P := by sorry
