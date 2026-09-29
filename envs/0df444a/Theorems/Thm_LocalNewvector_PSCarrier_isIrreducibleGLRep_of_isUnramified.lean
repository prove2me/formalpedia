-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified
-- name    : LocalNewvector.PSCarrier.isIrreducibleGLRep_of_isUnramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/ec89f9c2-7fe0-50f5-8554-10e48262c501
-- title:
--   Irreducibility of unramified principal series for GL₂(ℚₚ)
-- statement:
--   Let $p$ be a prime and let $\mu_1,\mu_2 \colon \mathbb{Q}_p^\times \to \mathbb{C}^\times$ be group homomorphisms which are unramified in the sense of [`LocalNewvector.IsUnramified`](def/LocalNewvector_CharConductor.html#L11), i.e. $\mu_i(u)=1$ for every unit $u$ with $\|u\|=1$. Let $\varpi$ denote the unit of $\mathbb{Q}_p$ given by the nonzero element $p$, and assume that the ratio $\mu_1(\varpi)\,\mu_2(\varpi)^{-1} \in \mathbb{C}^\times$ is different from $p$ and from $p^{-1}$. The conclusion is [`LocalNewvector.IsIrreducibleGLRep`](def/LocalNewvector_ConductorDatum.html#L102) for the carrier [`LocalNewvector.PSCarrier p μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), the $\mathbb{C}$-subspace of functions $f \colon \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ that are locally constant and satisfy $f(\mathrm{borelElem}\,p\,a_1\,a_2\,x \cdot g) = \mu_1(a_1)\,\mu_2(a_2)\,\mathrm{halfModulus}\,p\,a_1\,a_2 \cdot f(g)$ for all $a_1,a_2 \in \mathbb{Q}_p^\times$, $x \in \mathbb{Q}_p$ and $g \in \mathrm{GL}_2(\mathbb{Q}_p)$, where `borelElem` produces the corresponding Borel element and `halfModulus` is the normalising factor. Unfolded, the assertion is twofold: the carrier contains a vector $\ne 0$, and every $\mathbb{C}$-submodule $W$ of it which satisfies $g \bullet v \in W$ for all $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ and all $v \in W$ equals $\bot$ or $\top$.
--
--   This is the irreducibility half of the classical reducibility criterion for normalised principal series of $\mathrm{GL}_2$ over a $p$-adic field, specialised to unramified characters: reducibility occurs precisely when $\mu_1\mu_2^{-1} = |\cdot|^{\pm 1}$, which is excluded by the two hypotheses on $\mu_1(\varpi)\mu_2(\varpi)^{-1}$. It is used in the local analysis of newforms, in the results on adelic lifts whose local component at $p$ is an unramified principal series and on the behaviour of such components under quadratic twisting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalNewvector.PSCarrier.isIrreducibleGLRep_of_isUnramified (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (h₁ : LocalNewvector.IsUnramified p μ₁) (h₂ : LocalNewvector.IsUnramified p μ₂)
    (hγp : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ (p : ℂ))
    (hγp' : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) * ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ ≠ ((p : ℂ))⁻¹) :
    LocalNewvector.IsIrreducibleGLRep p (LocalNewvector.PSCarrier p μ₁ μ₂) := by sorry
