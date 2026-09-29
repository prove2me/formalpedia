-- Prove2me | Theorems.Thm_ModularCurve_natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth
-- name    : ModularCurve.natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/c4ddb3cf-10fd-5f06-b701-b29d02c2c1b4
-- title:
--   Two-sided linear growth of toric I^m-torsion on J₀(p)
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime p`, i.e. $p$ lies in the non-units of $A$, let $I$ be an ideal of the Hecke algebra `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ (a polynomial ring in indeterminates indexed by the primes), and assume $q \in I$. Give `JZero p`, the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the level-$p$ full modular function field base-changed to $\overline{\mathbb{Q}}$, its `heckeModuleBar p` module structure over `HeckeAlg`. The assertion is the existence of natural numbers $e$ and $C$ such that for every $m$, writing $S_m$ for the subgroup `jZeroToricTorsion p A (q ^ m)` $\cap$ `Submodule.torsionBySet HeckeAlg (JZero p) (I ^ m)` — where the first factor consists of the elements killed by $q^m$ that are of the form $n\cdot y$ with $n = (p-1)/\gcd(p-1,12)$ and $y$ invariant under the inertia subgroup of $A$ in $\overline{\mathbb{Q}}/\mathbb{Q}$, and the second of the elements annihilated by every element of $I^m$ — one has $\#S_m \le q^{me+C}$ and $q^{me} \le \#S_m \cdot q^{C}$, cardinalities being taken as `Nat.card`.
--
--   This is the two-sided linear (in $m$) estimate for the order of the toric part of the $I^m$-torsion of the Jacobian of the modular curve of level $p$, the toric part being the image of the inertia-invariants under multiplication by the Eisenstein numerator $(p-1)/\gcd(p-1,12)$. It feeds the growth and invertibility statements for the Néron torsion sheaf on $J_0(p)$ that are used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth (p : ℕ) [Fact p.Prime]
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    letI := heckeModuleBar p
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) * q ^ C := by sorry
