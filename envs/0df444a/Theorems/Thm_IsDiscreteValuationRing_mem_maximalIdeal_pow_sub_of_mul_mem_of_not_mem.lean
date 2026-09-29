-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
-- name    : IsDiscreteValuationRing.mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/a590a10f-fd8b-55bb-a809-413fd441b97e
-- title:
--   Valuation shift in a DVR: av∈𝔪^M, anotin𝔪^{k+1} give v∈𝔪^{M-k}
-- statement:
--   Let $\mathcal O$ be a commutative ring which is a domain and a discrete valuation ring, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal 𝒪`. Let $a, v \in \mathcal O$ and let $k, M$ be natural numbers. Assume that $a \notin \mathfrak m^{k+1}$, that is, the valuation of $a$ is at most $k$ (in particular $a \neq 0$), and that $a v \in \mathfrak m^{M}$. The conclusion is that $v \in \mathfrak m^{M-k}$, where $M - k$ is truncated subtraction of natural numbers, so that the assertion is vacuous when $k \geq M$ (then $\mathfrak m^{0} = \mathcal O$). Equivalently, in terms of the normalised valuation $v(\cdot)$ attached to $\mathcal O$: if $v(a) \le k$ and $v(a) + v(v) \ge M$, then $v(v) \ge M - k$.
--
--   An elementary divisibility estimate in a discrete valuation ring, used to shift the level at which a congruence holds. It is invoked in [`GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine), where a Frobenius relation of the form $(\alpha^2-1) \cdot V = 0$ modulo $\mathfrak m^{M}$ with $M$ exceeding the valuation of $\alpha^2-1$ by $m$ forces the vanishing of $V$ modulo $\mathfrak m^{m}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (a v : 𝒪) (k M : ℕ)
    (hk : a ∉ IsLocalRing.maximalIdeal 𝒪 ^ (k + 1))
    (h : a * v ∈ IsLocalRing.maximalIdeal 𝒪 ^ M) :
    v ∈ IsLocalRing.maximalIdeal 𝒪 ^ (M - k) := by sorry
