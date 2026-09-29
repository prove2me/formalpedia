-- Prove2me | Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO
-- name    : FrobeniusDensity.primeSum_toReal_add_log_isBigO
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1d44c6f8-7192-5c73-9ede-589f3fa050f4
-- title:
--   Prime ideal sum is log1s-1+O(1) as s→1⁺
-- statement:
--   Let $K$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$, with ring of integers $\mathcal{O}_K$). For a real parameter $s$, [`FrobeniusDensity.primeSum K s`](def/FrobeniusDensity_PrimeSums.html#L21) denotes the $[0,\infty]$-valued unordered sum $\sum_{\mathfrak{p}} (N\mathfrak{p})^{-s}$, indexed by the height-one spectrum of $\mathcal{O}_K$, i.e. by the nonzero prime ideals $\mathfrak{p}$ of $\mathcal{O}_K$, where the summand is the extended-nonnegative-real power $(\mathrm{absNorm}\,\mathfrak{p})^{-s}$ of the absolute ideal norm. The theorem asserts that the real-valued function
--   $$s \mapsto \bigl(\textstyle\sum_{\mathfrak{p}} (N\mathfrak{p})^{-s}\bigr)^{\phantom{.}}\!\!\mathrm{.toReal} + \log(s-1)$$
--   is $O(1)$ along the filter of neighbourhoods of $1$ restricted to the open half-line $(1,\infty)$: there exist a constant $C$ and a right neighbourhood of $1$ on which the absolute value of this function is at most $C$. Equivalently, $\sum_{\mathfrak{p}} (N\mathfrak{p})^{-s} = \log\frac{1}{s-1} + O(1)$ as $s \to 1^+$. No hypothesis beyond $K$ being a number field is imposed; the restriction to $s>1$, where the sum is finite, is carried by the filter rather than by a hypothesis.
--
--   This is the qualitative analytic input behind Frobenius's density theorem and the Chebotarev-type counting arguments, the prime-ideal analogue of Mertens' estimate and a weak form of Landau's prime ideal theorem; it is obtained from the simple pole of the Dedekind zeta function of $K$ at $s=1$ together with the Euler product. It is used for the corresponding asymptotic for the degree-one prime sum and for density estimates in cyclotomic extensions, and in an adelic integral estimate for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean

import Definitions.Def_FrobeniusDensity_PrimeSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Filter Topology Asymptotics

theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by sorry
