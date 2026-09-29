-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul
-- name    : ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/c1a48a62-e5f1-5d26-879d-031a66c51fd6
-- title:
--   I^m-torsion of J₀(p) at most the square of its toric part
-- statement:
--   Let $p$ and $q$ be primes with $q \neq p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to the set of nonunits of $A$, and let $I$ be an ideal of the Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ in indeterminates indexed by the primes, such that the image of $q$ in `HeckeAlg` lies in $I$. Equip $JZero\ p$, the degree-zero divisor class group $\mathrm{Pic}^0$ of the level-$p$ modular function field base changed to $\overline{\mathbb{Q}}$, with the `HeckeAlg`-module structure `heckeModuleBar p` given by the Hecke operators. The assertion is that there exists a natural number $C$ such that for every $m$ the cardinality (as a natural number, zero when infinite) of the subgroup of elements of $JZero\ p$ annihilated by every element of $I^m$ is at most the square of the cardinality of the intersection of that subgroup with $jZeroToricTorsion\ p\ A\ (q^m)$, times $q^C$. Here $jZeroToricTorsion\ p\ A\ (q^m)$ consists of the $q^m$-torsion points of $JZero\ p$ that are of the form $n \cdot y$ with $n = (p-1)/\gcd(p-1,12)$ and $y$ fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$. The exponent $C$ is uniform in $m$.
--
--   This is the Mazur-style comparison between the $I^m$-torsion of $J_0(p)$ and its toric part at a place above $p$, with the loss measured by a power of $q$ independent of $m$: the bound rests on the purely toric reduction of $J_0(p)$ at $p$ together with the action of tame inertia on $q$-power torsion. It is used as the input $\#J \le (\#T)^2 q^C$ for the linear-growth estimate for the Néron torsion data and for the companion cardinality bound involving reduction mod $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    letI := heckeModuleBar p
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup ≤
        Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ^ 2 * q ^ C := by sorry
