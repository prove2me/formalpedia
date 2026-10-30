-- Prove2me | Theorems.Thm_JuschenkoMonod_exists_invariantMean_mem_zero
-- name    : JuschenkoMonod.exists_invariantMean_mem_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:26:05.00235+00:00
-- url     : https://prove2.me/theorems/c8f803ac-0857-4f50-8c5c-c51622de6f04
-- title:
--   Theorem C — the W(ℤ)-action on finite sets of integers has an invariant mean giving full weight to the sets containing 0
-- statement:
--   There is a mean $m$ on the finite subsets of $\mathbf Z$ (a finitely additive probability measure on all collections of finite subsets) that is invariant under $W(\mathbf Z)$, acting by $E \mapsto g(E)$, and gives weight $1$ to the collection of finite sets containing $0$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 776, Theorem C

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

open scoped ENNReal Pointwise

namespace JuschenkoMonod

theorem exists_invariantMean_mem_zero :
    ∃ m : Set (Finset ℤ) → ℝ≥0∞, IsInvariantMean (IntervalExchange.wobbling ℤ) m ∧
      m {E | 0 ∈ E} = 1 := by
  sorry

end JuschenkoMonod
