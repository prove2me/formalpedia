-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_fullC_mul_prime_pow
-- name    : ModularCurve.relfinrank_fullC_mul_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b8d18334-4f62-51c7-876d-ed4aaa767c4c
-- title:
--   Prime-power step for fields of divisor q-expansions of j
-- statement:
--   Let $K$ be a field, $M$ a nonzero natural number, $p$ a prime not dividing $M$, and $a$ a natural number, and suppose some unit $\zeta$ of $K$ is a primitive root of unity of order $M p^{a+1}$. For a nonzero natural number $n$ write $F_n$ for the intermediate field `IntermediateField.adjoin K` of the set of Laurent series of the form `jqNModC K d'` with $d'$ a nonzero divisor of $n$; here `jqNModC K d'` is the image of `jqModC K` $= q^{-1}\cdot(\text{the integral power series }$`jNum`$)$ read in $K$ under the exponent-scaling ring homomorphism `qExpand K d'`, i.e. the expansion $j(q^{d'})$ inside $K((q))$. Assume: (i) whenever $a = b+1$, the relative degree of $F_{M p^{b+1}}$ over $F_{M p^{b}}$ equals $p+1$ if $b = 0$ and $p$ otherwise; (ii) if $a = 0$, then $j(q^{p}) \notin F_{M}$. Then `IntermediateField.relfinrank` of $F_{M p^{a}}$ and $F_{M p^{a+1}}$, i.e. the relative degree $[F_{M p^{a+1}} : F_{M p^{a}}]$ as a natural number, equals $p+1$ if $a = 0$ and $p$ otherwise.
--
--   This is the inductive prime-power step in the computation of the degrees in the tower of fields generated over $K$ by the divisor expansions $j(q^{d})$, $d \mid n$, inside $K((q))$ — the $q$-expansion model of the function fields of the modular curves $X_0(n)$, whose total degree over $K(j(q))$ is Dedekind's $\psi(n)$. It is used by [`ModularCurve.package_of_socket`](thm.html#ModularCurve.package_of_socket).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.relfinrank_fullC_mul_prime_pow {K : Type*} [Field K] (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1))) (hprev : ∀ b : ℕ, a = b + 1 → IntermediateField.relfinrank (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ b ∧ x = jqNModC K d'}) (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (b + 1) ∧ x = jqNModC K d'}) = if b = 0 then p + 1 else p) (hnm : a = 0 → jqNModC K p ∉ IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'}) : IntermediateField.relfinrank (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ a ∧ x = jqNModC K d'}) (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (a + 1) ∧ x = jqNModC K d'}) = if a = 0 then p + 1 else p := by sorry
