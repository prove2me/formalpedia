-- Prove2me | Theorems.Thm_ModularCurve_tsum_lambertTerm_eq
-- name    : ModularCurve.tsum_lambertTerm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/335f66df-f321-5b3a-a6e3-ee270f2d8537
-- title:
--   A formal Lambert series identity in K((q))
-- statement:
--   Let $K$ be a field, let $p$ be a natural number that is nonzero, and let $c : \mathbb{N} \to \mathbb{N}$ be an arbitrary sequence of natural numbers. Inside the field $K((q))$ of Laurent series over $K$ — realised as Hahn series over $\mathbb{Z}$ — write $Q :=$ `HahnSeries.single (p : ℤ) (1 : K)`, the monomial $q^{p}$. The assertion is the equality of the unconditional sum (a `tsum` for the valuation topology on $K((q))$) $$\sum_{n \in \mathbb{N}} c(n)\, \frac{Q^{n}}{1 - Q^{n}}$$ with the image of the integral power series $\sum_{m} \bigl(\sum_{d \mid m} c(d)\bigr) q^{m}$ under two ring homomorphisms: first `laurentOfInt K`, which applies $\mathbb{Z} \to K$ to the coefficients and views the resulting power series as a Laurent series, and then `qExpand K p`, the ring homomorphism of $K((q))$ obtained by pushing the exponent support forward along multiplication by $p$ on $\mathbb{Z}$, i.e. the substitution $q \mapsto q^{p}$. The index $n$ runs over all of $\mathbb{N}$; the term $n = 0$ contributes $0$, since $1 - Q^{0} = 0$ and division by zero is zero. On the right, the coefficient in degree $0$ is likewise $0$, the divisors of $0$ forming the empty set.
--
--   This is the classical Lambert series identity $\sum_n c(n) Q^n/(1-Q^n) = \sum_m \bigl(\sum_{d\mid m} c(d)\bigr) Q^m$, stated purely formally in the field of Laurent series. It is used by [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation) and [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation), where the sequences $c(n) = n^{3}$ and $c(n) = (5n^{3} + 7n^{5})/12$ turn the Lambert-type expressions into the divisor-sum series $a_{4}(q)$ and $a_{6}(q)$ of the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tsum_lambertTerm_eq.lean

import Definitions.Def_ModularCurve_TateFormal
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.tsum_lambertTerm_eq (K : Type*) [Field K] (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n : ℕ, ((c n : ℕ) : LaurentSeries K) *
        ((HahnSeries.single (p : ℤ) (1 : K)) ^ n / (1 - (HahnSeries.single (p : ℤ) (1 : K)) ^ n)) =
      qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) := by sorry
