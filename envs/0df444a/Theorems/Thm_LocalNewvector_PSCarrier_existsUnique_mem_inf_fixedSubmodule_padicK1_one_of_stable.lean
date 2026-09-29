-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
-- name    : LocalNewvector.PSCarrier.existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/05370b0f-0b84-51a7-a969-02b23b58fc0c
-- title:
--   Newvector with Iwahori values 1 and -p⁻¹
-- statement:
--   Let $p$ be a prime and let $\mu_1,\mu_2:\mathbb{Q}_p^\times\to\mathbb{C}^\times$ be group homomorphisms, each unramified in the sense of [`LocalNewvector.IsUnramified`](def/LocalNewvector_CharConductor.html#L11), i.e. $\mu_i(u)=1$ for every unit $u$ with $\|u\|=1$. Assume the ratio condition $\mu_1(p)\,\mu_2(p)^{-1}=p^{-1}$ in $\mathbb{C}$, where $p$ is viewed as the unit $\mathrm{mk}_0(p)$ of $\mathbb{Q}_p$. Let $W$ be a $\mathbb{C}$-submodule of [`LocalNewvector.PSCarrier p μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), the space of locally constant functions $f:\mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ satisfying $f(\mathtt{borelElem } p\,a_1\,a_2\,x\cdot g)=\mu_1(a_1)\mu_2(a_2)\,(\mathtt{halfModulus } p\,a_1\,a_2)\,f(g)$ for all units $a_1,a_2$, all $x\in\mathbb{Q}_p$ and all $g$; assume $W$ is stable under the $\mathrm{GL}_2(\mathbb{Q}_p)$-action ($g\cdot v\in W$ for all $g$ and all $v\in W$) and $W\neq 0$. Then there is exactly one $f$ in the carrier such that: $f$ lies in $W$ and is fixed by every element of [`LocalNewvector.padicK1 p 1`](def/LocalNewvector_CongruenceSubgroupK1.html#L161), the subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$ of images of matrices $y\in\mathrm{GL}_2(\mathbb{Z}_p)$ with $y_{10}\in p\mathbb{Z}_p$ and $y_{11}-1\in p\mathbb{Z}_p$; $f(1)=1$; and for every $k\in\mathrm{GL}_2(\mathbb{Z}_p)$, the value of $f$ at the image of $k$ in $\mathrm{GL}_2(\mathbb{Q}_p)$ equals $1$ if $k_{10}\in p\mathbb{Z}_p$, and equals $-p^{-1}$ otherwise.
--
--   This is the newvector statement of Casselman's theory in the case of a reducible unramified principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$ with $\mu_1/\mu_2(p)=p^{-1}$, where the invariant line for $K_1(p)$ is pinned down by its explicit values on the two Iwahori cosets in $\mathrm{GL}_2(\mathbb{Z}_p)$ ($1$ on the Iwahori coset, $-p^{-1}$ elsewhere); the nonzero stable subspace $W$ is thereby the special (Steinberg-twist) constituent or the whole space. It is used in the study of adelic lifts of cusp forms and of quadratic twists of newforms whose level is divisible by $p^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (h₁ : LocalNewvector.IsUnramified p μ₁) (h₂ : LocalNewvector.IsUnramified p μ₂)
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ = ((p : ℂ))⁻¹)
    (W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂)) (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W)
    (hb : W ≠ ⊥) :
    ∃! f : LocalNewvector.PSCarrier p μ₁ μ₂,
      f ∈ W ⊓ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 1) (LocalNewvector.PSCarrier p μ₁ μ₂) ∧
      LocalNewvector.PSCarrier.toFn p μ₁ μ₂ f 1 = 1 ∧
      ∀ k : GL (Fin 2) ℤ_[p],
        ((k : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∈ Ideal.span {(p : ℤ_[p])} →
          LocalNewvector.PSCarrier.toFn p μ₁ μ₂ f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k) = 1) ∧
        ((k : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∉ Ideal.span {(p : ℤ_[p])} →
          LocalNewvector.PSCarrier.toFn p μ₁ μ₂ f (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) k)
            = -((p : ℂ))⁻¹) := by sorry
