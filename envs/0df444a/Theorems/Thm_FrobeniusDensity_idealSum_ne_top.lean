-- Prove2me | Theorems.Thm_FrobeniusDensity_idealSum_ne_top
-- name    : FrobeniusDensity.idealSum_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/35a12b26-62d6-5420-9b37-b7c2c2961891
-- title:
--   Finiteness of the ideal sum sum_I (NI)^{-s} for s>1
-- statement:
--   Let $K$ be a field which is a number field, and let $s$ be a real number with $1 < s$. The quantity [`FrobeniusDensity.idealSum K s`](def/FrobeniusDensity_PrimeSums.html#L18) is the unconditional sum, taken in $[0,\infty]$, of the terms [`FrobeniusDensity.normRpow K s I`](def/FrobeniusDensity_PrimeSums.html#L15) over the subtype of ideals $I$ of the ring of integers $\mathcal{O}_K$ with $I \neq \bot$, where `normRpow K s I` is the extended-nonnegative-real power $(\operatorname{absNorm} I)^{-s}$, the absolute ideal norm being viewed in $\mathbb{R}_{\ge 0}^\infty$ and the exponent being $-s$. The assertion is that this sum is not $\top$, i.e. that $$\sum_{0 \neq I \subseteq \mathcal{O}_K} (N I)^{-s} < \infty.$$ Thus the statement is the absolute convergence of the Dedekind zeta series of $K$ in the half-line $s > 1$, formulated as a finiteness statement for an $\mathbb{R}_{\ge 0}^\infty$-valued sum over nonzero ideals, so that no separate summability hypothesis has to be carried.
--
--   This is the convergence of the Dedekind zeta function $\zeta_K(s)$ for real $s > 1$, in the form needed to manipulate the corresponding sums inside $[0,\infty]$. It underlies the prime-sum estimates of the Frobenius density argument, being cited for the big-$O$ comparisons of the degree-one and full prime sums with $-\log(s-1)$ and for the summability of the degree-one terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean

import Definitions.Def_FrobeniusDensity_PrimeSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.idealSum_ne_top
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by sorry
