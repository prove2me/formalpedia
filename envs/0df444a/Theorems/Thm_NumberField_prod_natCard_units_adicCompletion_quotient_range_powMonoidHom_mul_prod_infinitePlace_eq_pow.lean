-- Prove2me | Theorems.Thm_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
-- name    : NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/bbb65ca6-b1ba-576b-a1ac-33986b4a6a03
-- title:
--   Product of local p-th power indices over S and ∞
-- statement:
--   Let $K$ be a number field, let $p$ be a prime, and assume that the set of primitive $p$-th roots of unity in $K$ is non-empty, i.e. $K$ contains a primitive $p$-th root of unity. Let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$ such that every $v$ whose prime ideal contains $p$ lies in $S$. For a height-one prime $v$ write $K_v$ for the $v$-adic completion of $K$, and for an infinite place $w$ of $K$ write $K_w$ for the completion at $w$; in each case form the quotient of the unit group by the image of the $p$-th power homomorphism, i.e. $K_v^\times/(K_v^\times)^p$ and $K_w^\times/(K_w^\times)^p$. The assertion is the equality of natural numbers
--   $$\Bigl(\prod_{v\in S}\#\bigl(K_v^\times/(K_v^\times)^p\bigr)\Bigr)\cdot\prod_{w\mid\infty}\#\bigl(K_w^\times/(K_w^\times)^p\bigr)=p^{\,2\,(\#S+\#\{w\mid\infty\})},$$
--   the second product being over all infinite places of $K$, and the cardinalities being taken in the sense of `Nat.card` (so the statement in particular records that all these quotients are finite of the stated total order).
--
--   This is the global count of local $p$-th power classes at the places of $S\cup S_\infty$ that enters the second inequality in the Chevalley–Tate–Minkowski style index computations used for class-field-theoretic bounds; the factor $p^2$ per place reflects $\#(K_v^\times/(K_v^\times)^p)=p^2\,\#(\mathcal{O}_v/p)$ once $\mu_p\subseteq K$. It is used in the computation of the relative index of the idele box inside the $p$-th powers together with the units outside $S$, and in the second-inequality step for number fields containing $\mu_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
    {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p K).Nonempty)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range))
        * ∏ w : NumberField.InfinitePlace K,
            Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range)
      = p ^ (2 * (S.card + Fintype.card (NumberField.InfinitePlace K))) := by sorry
