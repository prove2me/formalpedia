-- Prove2me | Theorems.Thm_ModularCurve_arithmeticGalois_smul_sub_mem_inertiaInvariantPoints
-- name    : ModularCurve.arithmeticGalois_smul_sub_mem_inertiaInvariantPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/a7e2feda-edb6-5029-968e-25fb73ed8b1a
-- title:
--   Unipotence of inertia on prime-to-p torsion of J₀(p)
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ lying over $p$ in the sense that the image of $p$ lies in the set of nonunits of $A$. The assertion is then universally quantified over: a natural number $m$ with $m \neq 0$ and $p \nmid m$; an automorphism $\sigma$ of the algebraic closure of $\mathbb{Q}$ over $\mathbb{Q}$ belonging to `A.inertiaSubgroupIn ℚ`, that is, to the image in the full automorphism group of the inertia subgroup of $A$ inside the decomposition subgroup of $A$; and a point $x$ of `JZero p`, the group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldBar p`, i.e. the quotient of the degree-zero divisors by the principal divisors of the base change to the algebraic closure of $\mathbb{Q}$ of the full modular function field of level $p$, subject to $x \in$ `jZeroTorsion p m`, i.e. $m \cdot x = 0$. The conclusion is that $\sigma \cdot x - x$ lies in `inertiaInvariantPoints p A`, the subgroup of those $y$ with $\tau \cdot y = y$ for every $\tau$ in `A.inertiaSubgroupIn ℚ`; equivalently $(\tau - 1)(\sigma - 1)$ annihilates the $m$-torsion of $J_0(p)$.
--
--   This is the unipotence-of-echelon-two statement for the action of inertia at $p$ on the prime-to-$p$ torsion of a semistable abelian variety, here for the Jacobian $J_0(p)$: inertia at $p$ acts through a group whose augmentation ideal squares to zero on $J_0(p)[m]$ for $p \nmid m$. It is used in the project as the weak half of the assertion that the variation $(\sigma-1)J_0(p)[m]$ lies in the toric part, feeding the existence of an inertia element acting non-trivially on prime-to-$p$ torsion and the cardinality estimate for the toric torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithmeticGalois_smul_sub_mem_inertiaInvariantPoints.lean

import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.arithmeticGalois_smul_sub_mem_inertiaInvariantPoints
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ (m : ℕ) (hm0 : m ≠ 0) (hpm : ¬ p ∣ m)
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
      (x : JZero p) (hx : x ∈ jZeroTorsion p m),
      σ • x - x ∈ inertiaInvariantPoints p A := by sorry
