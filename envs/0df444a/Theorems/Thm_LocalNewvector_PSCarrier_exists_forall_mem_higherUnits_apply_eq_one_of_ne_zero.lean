-- Prove2me | Theorems.Thm_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
-- name    : LocalNewvector.PSCarrier.exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/2d26b2a2-4bca-5f30-8810-07263c9c29e5
-- title:
--   Characters of a nonzero principal series are smooth
-- statement:
--   Let $p$ be a prime and let $\mu_1,\mu_2 : \mathbb{Q}_p^{\times} \to \mathbb{C}^{\times}$ be monoid homomorphisms, with no continuity hypothesis imposed. Let $F$ be an element of [`LocalNewvector.PSCarrier p μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), that is, of the $\mathbb{C}$-submodule of functions $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ consisting of those $f$ that are locally constant and satisfy the transformation law $f(\,b(a_1,a_2,x)\,g) = \mu_1(a_1)\,\mu_2(a_2)\,\delta^{1/2}(a_1,a_2)\,f(g)$ for all $a_1,a_2 \in \mathbb{Q}_p^{\times}$, $x \in \mathbb{Q}_p$ and $g \in \mathrm{GL}_2(\mathbb{Q}_p)$, where $b(a_1,a_2,x)$ denotes the upper-triangular matrix `borelElem p a₁ a₂ x` with diagonal $(a_1,a_2)$ and upper-right entry $x$, and $\delta^{1/2}$ is the factor `halfModulus p a₁ a₂`. Assume $F \neq 0$. Then there is a natural number $c$ such that for every $u \in$ [`LocalNewvector.higherUnits p c`](def/LocalNewvector_CharConductor.html#L62), i.e. every unit $u$ of $\mathbb{Q}_p$ with $\|u\| = 1$ and, when $c \neq 0$, $\|u - 1\| \leq p^{-c}$, one has $\mu_1(u) = 1$ and $\mu_2(u) = 1$.
--
--   This is the statement that the inducing characters of a principal series representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ are automatically trivial on a higher unit group $1 + p^c\mathbb{Z}_p$ as soon as the induced space contains a nonzero (locally constant) vector; in particular such characters have finite conductor. It is used in the local analysis of newforms, for instance in the identification of the inertial behaviour of the associated $p$-adic Galois representation and in the construction of primitive forms with unramified local parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_PSCarrier_exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero.lean

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalNewvector.PSCarrier.exists_forall_mem_higherUnits_apply_eq_one_of_ne_zero
    (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) (F : LocalNewvector.PSCarrier p μ₁ μ₂)
    (hF : F ≠ 0) :
    ∃ c : ℕ, ∀ u ∈ LocalNewvector.higherUnits p c, μ₁ u = 1 ∧ μ₂ u = 1 := by sorry
