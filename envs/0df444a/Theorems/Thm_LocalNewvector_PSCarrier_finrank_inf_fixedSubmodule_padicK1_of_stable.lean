-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable
-- name    : LocalNewvector.PSCarrier.finrank_inf_fixedSubmodule_padicK1_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/559e9d19-5b31-5724-a8da-4e0aacc9845f
-- title:
--   Casselman's level count for the special subrepresentation at K₁(p^m)
-- statement:
--   Let $p$ be a prime, let $\mu_1,\mu_2:\mathbb{Q}_p^\times\to\mathbb{C}^\times$ be multiplicative characters and let $c\in\mathbb{N}$ be such that both $\mu_1$ and $\mu_2$ satisfy [`LocalNewvector.HasCharConductor p · c`](def/LocalNewvector_CharConductor.html#L92), i.e. each is trivial on `higherUnits p c` $=\{u:\|u\|=1$ and ($c=0$ or $\|u-1\|\le p^{-c})\}$ while for every $m<c$ it is non-trivial on some element of `higherUnits p m`. Assume the ratio condition $\mu_1(p)\,\mu_2(p)^{-1}=p^{-1}$ in $\mathbb{C}$, where $p$ is regarded as a unit of $\mathbb{Q}_p$. Let $W$ be a $\mathbb{C}$-subspace of [`LocalNewvector.PSCarrier p μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), the space of locally constant $f:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ with $f(\,$`borelElem p a₁ a₂ x`$\cdot g)=\mu_1(a_1)\mu_2(a_2)\,$`halfModulus p a₁ a₂`$\,f(g)$ for all $a_1,a_2\in\mathbb{Q}_p^\times$, $x\in\mathbb{Q}_p$ and $g$, and suppose $W$ is stable under the $\mathrm{GL}_2(\mathbb{Q}_p)$-action ($g\cdot v\in W$ for all $g$ and all $v\in W$), with $W\neq 0$ and $W\neq$ the whole space. Then for every $m\in\mathbb{N}$ the intersection of $W$ with the subspace of vectors fixed by every element of [`LocalNewvector.padicK1 p m`](def/LocalNewvector_CongruenceSubgroupK1.html#L161) — the subgroup of matrices coming entrywise from some $y\in\mathrm{GL}_2(\mathbb{Z}_p)$ with $y_{10}\in(p^m)$ and $y_{11}-1\in(p^m)$ — has $\mathbb{C}$-dimension $m+1-\max(1,2c)$, the subtraction being truncated subtraction of natural numbers (so the value is $0$ once $m+1\le\max(1,2c)$).
--
--   This is Casselman's count of $K_1(p^m)$-fixed vectors for the special representation of $\mathrm{GL}_2(\mathbb{Q}_p)$: under the stated ratio condition the principal series attached to $(\mu_1,\mu_2)$ is reducible, any proper nonzero invariant subspace is the twisted Steinberg constituent, its conductor exponent is $\max(1,2c)$, and each further level adds one dimension. It is used in the comparison of the local conductor exponents of a primitive cusp form with the factorisation data of its associated local representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.finrank_inf_fixedSubmodule_padicK1_of_stable (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ}
    (h₁ : LocalNewvector.HasCharConductor p μ₁ c) (h₂ : LocalNewvector.HasCharConductor p μ₂ c)
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ = ((p : ℂ))⁻¹)
    (W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂)) (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W)
    (hb : W ≠ ⊥) (ht : W ≠ ⊤) (m : ℕ) :
    Module.finrank ℂ
      ↥(W ⊓ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p m) (LocalNewvector.PSCarrier p μ₁ μ₂))
        = m + 1 - max 1 (2 * c) := by sorry
