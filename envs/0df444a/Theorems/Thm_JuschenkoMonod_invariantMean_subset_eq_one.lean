-- Prove2me | Theorems.Thm_JuschenkoMonod_invariantMean_subset_eq_one
-- name    : JuschenkoMonod.invariantMean_subset_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:26:37.675303+00:00
-- url     : https://prove2.me/theorems/bed94ffa-1cd4-4707-a464-fc6d964c7a73
-- title:
--   p. 776 — a mean as in Theorem C gives full weight to the sets containing any given finite set E
-- statement:
--   Let $m$ be a $W(\mathbf Z)$-invariant mean on the finite subsets of $\mathbf Z$ that gives weight $1$ to the collection of sets containing $0$. Then for every finite set $E_0 \subseteq \mathbf Z$, $m$ gives weight $1$ to the collection of finite sets containing $E_0$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 776, the remark after Theorem C

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

open scoped ENNReal Pointwise

namespace JuschenkoMonod

theorem invariantMean_subset_eq_one (m : Set (Finset ℤ) → ℝ≥0∞)
    (hm : IsInvariantMean (IntervalExchange.wobbling ℤ) m) (h0 : m {E | 0 ∈ E} = 1)
    (E₀ : Finset ℤ) : m {E | E₀ ⊆ E} = 1 := by
  sorry

end JuschenkoMonod
