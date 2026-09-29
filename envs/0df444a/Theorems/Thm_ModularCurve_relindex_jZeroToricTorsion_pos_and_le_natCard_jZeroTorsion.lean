-- Prove2me | Theorems.Thm_ModularCurve_relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion
-- name    : ModularCurve.relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/94ef682f-c9e0-53b5-92c1-658a547faffd
-- title:
--   Inertia-fixed q-power torsion is toric up to bounded index
-- statement:
--   Let $p$ and $q$ be primes with $q \neq p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$, viewed in $\overline{\mathbb{Q}}$, is a nonunit of $A$, and let $k$ be a natural number. Write $J =$ `JZero p` for the degree-zero Picard group $\operatorname{Pic}^0$ of the level-$p$ modular function field over $\overline{\mathbb{Q}}$, carrying its action of $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$; for $m \in \mathbb{N}$ let $J[m]$ be the subgroup of elements killed by $m$, let $H =$ `inertiaInvariantPoints p A` be the subgroup of elements fixed by every element of the image in $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside its decomposition subgroup, and let $n = (p-1)/\gcd(p-1,12)$ be `eisensteinNumerator p`. With the toric $m$-torsion defined as $T[m] = J[m] \cap nH$, the assertion is that the relative index of $T[q^k]$ in $J[q^k] \cap H$, that is the index of $T[q^k] \cap (J[q^k] \cap H)$ in $J[q^k] \cap H$, is nonzero, so the index is finite, and is bounded above by $\#J[n]$, a bound independent of $k$.
--
--   This is a quantitative, uniform-in-$k$ comparison between the inertia-invariant $q$-power torsion of $J_0(p)$ at a place above $p$ and its toric part $nH$, with $n$ the numerator of $(p-1)/12$ appearing in Mazur's study of the Eisenstein ideal; it is a bounded-index substitute for the sharper statement that the index divides $n$. It is used in [`ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul`](thm.html#ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul), where a bound on $q$-power torsion subgroups is derived.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroToricTorsion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (k : ℕ) :
    0 < (jZeroToricTorsion p A (q ^ k)).relIndex (jZeroTorsion p (q ^ k) ⊓ inertiaInvariantPoints p A) ∧
      (jZeroToricTorsion p A (q ^ k)).relIndex (jZeroTorsion p (q ^ k) ⊓ inertiaInvariantPoints p A)
        ≤ Nat.card ↥(jZeroTorsion p (eisensteinNumerator p)) := by sorry
