-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
-- name    : ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/34425200-a90f-5a24-98eb-57a2bd26597e
-- title:
--   Inertia at p acts on q-power torsion of J₀(p) through one element
-- statement:
--   Let $p$ and $q$ be primes with $q \ne p$, and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $A$, so that $A$ lies over the rational prime $p$. Write $I_A =$ `A.inertiaSubgroupIn ℚ` for the subgroup of $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ obtained as the image of the inertia subgroup of $A$ inside the decomposition subgroup of $A$ under the inclusion of that decomposition subgroup. Let `JZero p` denote the degree-zero divisor class group $\mathrm{Pic}^0$ over $\overline{\mathbb Q}$ of the modular function field of level $p$, with its action of $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and for $m \in \mathbb N$ let `jZeroTorsion p m` be the subgroup of elements killed by $m$. The assertion is that there is a single element $\sigma_0 \in I_A$ with the following property: for every $k \in \mathbb N$ and every $x \in$ `jZeroTorsion p (q ^ k)`, if $\sigma_0 \cdot x = x$ then $\sigma \cdot x = x$ for all $\sigma \in I_A$. Thus the fixed points of $\sigma_0$ on the $q^k$-torsion coincide with the $I_A$-invariants, uniformly in $k$.
--
--   This expresses that inertia at $p$ acts on the $q$-power torsion of $J_0(p)$ through a single element, a consequence of the unipotence of the inertia action coming from semistable reduction at $p$ together with the tame $q$-adic character of the resulting quotient. It is used in the bounds comparing the toric torsion with the full $q^k$-torsion, namely in [`ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul`](thm.html#ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul) and [`ModularCurve.relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion`](thm.html#ModularCurve.relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_ModularCurve_JZeroToricTorsion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ σ₀ ∈ A.inertiaSubgroupIn ℚ, ∀ (k : ℕ),
      ∀ x ∈ jZeroTorsion p (q ^ k), σ₀ • x = x →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x := by sorry
