-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
-- name    : LocalNewvector.PSCarrier.exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c4742f42-fcdb-5e7a-b625-d1daa9c17dab
-- title:
--   Invariant subspaces of the principal series B(μ₁,μ₁|·|)
-- statement:
--   Let $p$ be a prime, let $\mu_1,\mu_2:\mathbb{Q}_p^{\times}\to\mathbb{C}^{\times}$ be group homomorphisms and let $c$ be a natural number. Assume: (i) `HasCharConductor p μ₁ c`, i.e. $\mu_1$ is trivial on the set of units $u$ with $\|u\|=1$ and ($c=0$ or $\|u-1\|\le p^{-c}$), while for every $m<c$ there is a unit $u$ with $\|u\|=1$ and ($m=0$ or $\|u-1\|\le p^{-m}$) with $\mu_1(u)\neq 1$; (ii) `IsUnramified p (μ₁⁻¹ * μ₂)`, i.e. $\mu_1^{-1}\mu_2$ is trivial on every unit of norm $1$; (iii) $\mu_1(p)\,\mu_2(p)^{-1}=p$ in $\mathbb{C}$, the uniformiser $p$ being taken as a unit of $\mathbb{Q}_p$. Then there is an element $T$ of `PSCarrier p μ₁ μ₂`, the space of locally constant $F:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ satisfying $F(\mathrm{borelElem}(a_1,a_2,x)\,g)=\mu_1(a_1)\mu_2(a_2)\sqrt{\|a_1\|/\|a_2\|}\,F(g)$ for all $a_1,a_2\in\mathbb{Q}_p^{\times}$, $x\in\mathbb{Q}_p$ and $g$, such that: the underlying function of $T$ is $g\mapsto \mu_1(\det g)\sqrt{\|\det g\|}$; and a $\mathbb{C}$-submodule $W$ of this space satisfies $g\cdot v\in W$ for all $g\in\mathrm{GL}_2(\mathbb{Q}_p)$ and all $v\in W$ if and only if $W=\bot$, or $W=\mathbb{C}T$, or $W=\top$.
--
--   This is the case $\mu_1\mu_2^{-1}=|\cdot|^{-1}$ of the classification of the $\mathrm{GL}_2(\mathbb{Q}_p)$-invariant subspaces of a principal series in normalised induction: the space is reducible, with the unique proper non-zero invariant subspace the line on which the group acts by the character $\mu_1(\det)|\det|^{1/2}$, the quotient being the twisted special representation. It is used in the analysis of local components of primitive forms, through [`CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified`](thm.html#CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalNewvector.PSCarrier.exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
    (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ}
    (h₁ : LocalNewvector.HasCharConductor p μ₁ c)
    (hrat : LocalNewvector.IsUnramified p (μ₁⁻¹ * μ₂))
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) *
        ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹
          = (p : ℂ)) :
    ∃ T : LocalNewvector.PSCarrier p μ₁ μ₂,
      (∀ g : GL (Fin 2) ℚ_[p], LocalNewvector.PSCarrier.toFn p μ₁ μ₂ T g =
        (μ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
          LocalNewvector.halfModulus p (Matrix.GeneralLinearGroup.det g) 1) ∧
      ∀ W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂),
        (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) ↔
          (W = ⊥ ∨ W = Submodule.span ℂ {T} ∨ W = ⊤) := by sorry
