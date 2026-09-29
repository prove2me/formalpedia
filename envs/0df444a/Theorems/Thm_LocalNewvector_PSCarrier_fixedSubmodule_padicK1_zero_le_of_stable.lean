-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_le_of_stable
-- name    : LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_le_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/31586c4a-a5f6-51e4-a2db-3987aa807636
-- title:
--   Spherical vectors lie in every nonzero stable subspace
-- statement:
--   Let $p$ be a prime and let $\mu_1,\mu_2 \colon \mathbb{Q}_p^\times \to \mathbb{C}^\times$ be group homomorphisms, each assumed unramified in the sense of [`LocalNewvector.IsUnramified`](def/LocalNewvector_CharConductor.html#L11), i.e. $\mu_i(u) = 1$ for every unit $u$ of $\mathbb{Q}_p$ with $\|u\| = 1$. Assume further that the values at the uniformiser satisfy $\mu_1(p)\,\mu_2(p)^{-1} = p$ in $\mathbb{C}$, where $p$ is viewed as a unit of $\mathbb{Q}_p$. The ambient space is [`LocalNewvector.PSCarrier p μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), the principal series realised as the $\mathbb{C}$-subspace of functions $f \colon \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ that are locally constant and satisfy $f(\mathrm{borelElem}(a_1,a_2,x)\, g) = \mu_1(a_1)\mu_2(a_2)\cdot \mathrm{halfModulus}(a_1,a_2)\cdot f(g)$ for all $a_1,a_2 \in \mathbb{Q}_p^\times$, $x \in \mathbb{Q}_p$ and $g \in \mathrm{GL}_2(\mathbb{Q}_p)$, with its $\mathrm{GL}_2(\mathbb{Q}_p)$-action. Let $W$ be a $\mathbb{C}$-subspace of this carrier which is stable, i.e. $g \cdot v \in W$ for all $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ and $v \in W$, and assume $W \neq 0$. The conclusion is that $W$ contains the submodule of vectors fixed by every element of [`LocalNewvector.padicK1 p 0`](def/LocalNewvector_CongruenceSubgroupK1.html#L161), that is, of vectors $v$ with $g \cdot v = v$ for all $g$ in the image of $\mathrm{GL}_2(\mathbb{Z}_p)$ in $\mathrm{GL}_2(\mathbb{Q}_p)$ (for $n = 0$ the two congruence conditions cut out by `congruenceK1` are vacuous).
--
--   This identifies the spherical line as contained in the socle of the unramified principal series at the reducible point $\mu_1(p)/\mu_2(p) = p$, where the one-dimensional constituent is the subrepresentation and the special representation the quotient; by [`LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1`](thm.html#LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1) the fixed space at level $0$ is one-dimensional for unramified $\mu_1,\mu_2$. It is used in the local analysis of newvectors behind the results on adelic lifts of newforms and on quadratic twists lowering the exponent of the conductor at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_fixedSubmodule_padicK1_zero_le_of_stable.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.fixedSubmodule_padicK1_zero_le_of_stable (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    (h₁ : LocalNewvector.IsUnramified p μ₁) (h₂ : LocalNewvector.IsUnramified p μ₂)
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) *
        ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ = (p : ℂ))
    (W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂)) (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W)
    (hb : W ≠ ⊥) :
    LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p 0) (LocalNewvector.PSCarrier p μ₁ μ₂) ≤ W := by sorry
