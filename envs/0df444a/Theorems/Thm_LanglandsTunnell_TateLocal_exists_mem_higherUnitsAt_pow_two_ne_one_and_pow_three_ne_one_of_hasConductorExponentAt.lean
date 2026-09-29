-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
-- name    : LanglandsTunnell.TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d1a05fb0-f9f0-5b40-984a-d79f7f5a3a38
-- title:
--   Non-triviality of χ² and χ³ on units of level m
-- statement:
--   Let $p$ be a height-one prime of the ring of integers $\mathcal O_{\mathbb Q} = \mathbb Z$, let $\chi$ be a homomorphism of monoids from the unit group of the $p$-adic completion $\mathbb Q_p$ of $\mathbb Q$ to $\mathbb C^\times$, and let $k_p$ be a natural number such that `HasConductorExponentAt` holds for $\chi$ at $p$ with value $k_p$, i.e. $\chi$ is trivial on the set `higherUnitsAt` of level $k_p$, and for every $m < k_p$ there is an element of `higherUnitsAt` of level $m$ on which $\chi$ is non-trivial. Here `higherUnitsAt` of level $n$ consists of those units $u$ of $\mathbb Q_p$ with $\mathrm v(u) = 1$ and, unless $n = 0$, also $\mathrm v(u - 1) \le \exp(-n)$, the valuation being the canonical one on the completion. Then for every natural number $m$ with $m + 4 \le k_p$ there exists $s$ in `higherUnitsAt` of level $m$ with $\chi(s)^2 \ne 1$, and there exists $s$ in `higherUnitsAt` of level $m$ with $\chi(s)^3 \ne 1$.
--
--   This is the standard statement that a character of $\mathbb Q_p^\times$ of exact conductor exponent $k_p$ remains non-trivial, after squaring or cubing, on the units congruent to $1$ modulo $p^m$ as soon as $m + 4 \le k_p$, the gap $4$ absorbing the loss incurred by extracting square and cube roots of principal units. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where the central and Levi unit groups act through $\chi^2$ and $\chi^3$, to obtain finiteness of the relevant torus action for deeply twisted characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ)
    (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (m : ℕ) (hm : m + 4 ≤ kp) :
    (∃ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ 2 ≠ 1) ∧
    (∃ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ 3 ≠ 1) := by sorry
