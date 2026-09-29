-- Prove2me | Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
-- name    : NumberField.natCard_sUnit_quotient_range_powMonoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4956b3f7-4628-5304-88c9-98a52854077e
-- title:
--   Order of U_S/U_Sⁿ when μₙ ⊆ K
-- statement:
--   Let $K$ be a number field, let $S$ be a set of height-one primes of the ring of integers $\mathcal{O}_K$ which is finite, and let $n$ be a natural number such that the set $\mathrm{primitiveRoots}\ n\ K$ is non-empty, i.e. $K$ contains a primitive $n$-th root of unity (this forces $n > 0$). Write $S.\mathrm{unit}\ K$ for the group of $S$-units of $K$, the subgroup of $K^{\times}$ consisting of those $x$ whose valuation at every height-one prime $v \notin S$ equals $1$. The assertion is that the quotient of this group by the image of the $n$-th power endomorphism `powMonoidHom n`, i.e. by the subgroup of $n$-th powers of $S$-units, has cardinality (in the `Nat.card` sense, so the equality also records finiteness, $n$ being positive)
--   $$\#\bigl(U_S/U_S^{\,n}\bigr) = n^{\,\#S + \mathrm{rank}(K) + 1},$$
--   where $\#S$ is the number of primes in $S$ and $\mathrm{rank}(K) = r_1 + r_2 - 1$ is the rank of the unit group of $\mathcal{O}_K$; the exponent is thus $\#S + r_1 + r_2$.
--
--   This is the index computation attached to the Dirichlet–Chevalley–Hasse $S$-unit theorem: for $K$ containing $\mu_n$, the group of $S$-units modulo $n$-th powers has order $n^{\#S+r_1+r_2}$. It supplies the local-to-global unit index entering the second inequality of class field theory, and is used in the statements [`NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots`](thm.html#NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots) and [`NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top`](thm.html#NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.natCard_sUnit_quotient_range_powMonoidHom (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite S]
    {n : ℕ} (hμ : (primitiveRoots n K).Nonempty) :
    Nat.card (↥(S.unit K) ⧸ (powMonoidHom n : ↥(S.unit K) →* ↥(S.unit K)).range)
      = n ^ (Nat.card S + NumberField.Units.rank K + 1) := by sorry
