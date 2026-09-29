-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
-- name    : LanglandsTunnell.CubicInduction.exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/2c7bb25a-9a75-54a5-812f-45eee0eb2d61
-- title:
--   Characters agreeing on local units differ by an unramified twist
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_v$ denotes the $v$-adic completion of $\mathbb{Q}$, and let $\chi,\chi' \colon \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be multiplicative maps (monoid homomorphisms of unit groups, with no continuity required). Assume that $\chi$ and $\chi'$ agree on every unit $u$ of $\mathbb{Q}_v$ such that both $u$ and $u^{-1}$ lie in the $v$-adic valuation ring, i.e. on the units of the ring of integers of $\mathbb{Q}_v$. The conclusion is the existence of a complex number $c$ such that for every $a \in \mathbb{Q}_v^\times$ one has $\chi(a) = \chi'(a)\cdot\big(\mathrm{modulus}(a)\big)^{-c}$ as an identity of complex numbers, where $\mathrm{modulus}(a)$ is the module of the locally compact field $\mathbb{Q}_v$ at $a$ — defined to be $0$ for $a = 0$ and otherwise the scaling factor by which multiplication by $a$ distorts Haar measure — viewed as a nonnegative real and then as a complex number, and the power is the complex power $z \mapsto z^{-c}$. Thus the two characters differ by the unramified character $a \mapsto |a|_v^{-c}$.
--
--   This is the standard statement that two characters of a nonarchimedean local field agreeing on the units of the valuation ring differ by an unramified twist, namely by a complex power of the normalised absolute value. It is used in the place-by-place comparison of a local character with the local component of a global admissible twist in the cubic-induction part of the Langlands–Tunnell argument, and is cited in the identification of the local zeta factors attached to a cubic induction datum at the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (h : ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ u = χ' u) :
    ∃ c : ℂ, ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((χ' a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c) := by sorry
