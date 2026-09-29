-- Prove2me | Theorems.Thm_ModularCurve_tsum_of_coeff_lt_eq_zero
-- name    : ModularCurve.tsum_of_coeff_lt_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/71a6b030-2d21-5b7a-8a27-35521546503a
-- title:
--   Coefficientwise summation in K((q)) for growing q-orders
-- statement:
--   Let $K$ be a field and let $K((q))$ be Mathlib's field of formal Laurent series over $K$, carrying the topology induced by its $q$-adic valuation. Let $\delta$ be a natural number with $0 < \delta$, and let $f : \mathbb{N} \to K((q))$ be a sequence of Laurent series subject to the vanishing condition that for every $N \in \mathbb{N}$ and every $m \in \mathbb{Z}$ with $m < N\delta$ the coefficient of $q^m$ in $f_N$ is zero, i.e. $f_N$ is supported in degrees $\ge N\delta$. Let $g \in K((q))$ be a Laurent series whose coefficients are given, for every $m \in \mathbb{Z}$, by the finite sum $g_m = \sum_{N=0}^{\lfloor m^{+}/\delta\rfloor} (f_N)_m$, where $m^{+}$ denotes $\max(m,0)$ (so that for $m < 0$ the sum has the single term $N = 0$) and the quotient is natural-number division. The conclusion is that the unconditional sum $\sum'_{N} f_N$, the `tsum` of the sequence in the topological additive group $K((q))$, equals $g$. In particular the sequence is summable and its sum is computed coefficient by coefficient.
--
--   This is the formal summation principle for power series whose $q$-orders tend to infinity: under a linear lower bound $N\delta$ on the order of the $N$-th term, the series converges in the $q$-adic topology and each coefficient of the sum is a finite sum of coefficients. It is used to evaluate $q$-expansions with terms of growing order, and is cited in the verification of the defining equations [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation) and [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation) for the Tate curve and its toric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tsum_of_coeff_lt_eq_zero.lean

import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.tsum_of_coeff_lt_eq_zero {K : Type*} [Field K] {δ : ℕ} (hδ : 0 < δ) (f : ℕ → LaurentSeries K) (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0) (g : LaurentSeries K) (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) : ∑' N, f N = g := by sorry
