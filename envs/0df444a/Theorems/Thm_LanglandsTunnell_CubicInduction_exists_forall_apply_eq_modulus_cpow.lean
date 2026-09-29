-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow
-- name    : LanglandsTunnell.CubicInduction.exists_forall_apply_eq_modulus_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/27c504d2-d9ee-5340-83fa-b240673becfb
-- title:
--   Unramified characters of ℚᵥ^× are powers of the modulus
-- statement:
--   Let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, let $\mathbb{Q}_v$ denote the $v$-adic completion of $\mathbb{Q}$, and let $\chi : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be a homomorphism of groups. Assume $\chi$ is unramified in the following sense: $\chi(t) = 1$ for every unit $t$ of $\mathbb{Q}_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring $\mathcal{O}_v$ (the `adicCompletionIntegers`), i.e. $\chi$ is trivial on $\mathcal{O}_v^\times$. Then there exists a single complex number $s_0$ such that for every $a \in \mathbb{Q}_v^\times$ two things hold: first, the real number $\mathrm{modulus}(a)$ — defined as the distributive Haar character $\mathrm{distribHaarChar}$ of the scaling action of $a$, the nonnegative real by which left Haar measure is scaled by multiplication by $a$, with value $0$ at $a = 0$ — is nonzero as a complex number; and second, $\chi(a) = \mathrm{modulus}(a)^{s_0}$, the complex power of the (coerced) real modulus. Thus an unramified character of $\mathbb{Q}_v^\times$ is a fixed complex power of the normalised absolute value.
--
--   This is the standard classification of unramified characters of a non-archimedean local field used in Tate's local theory: on $\mathbb{Q}_v^\times$ such a character is determined by its value on a uniformiser and equals $|\cdot|_v^{s_0}$. It feeds into the analysis of local zeta integrals and functional equations in the cubic-induction part of the Langlands–Tunnell argument, being cited by the results assembling the global functional equation from local root numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_forall_apply_eq_modulus_cpow
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ t : (v.adicCompletion ℚ)ˣ, (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ t = 1) :
    ∃ s₀ : ℂ, ∀ a : (v.adicCompletion ℚ)ˣ,
      ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 ∧
      ((χ a : ℂˣ) : ℂ) = ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s₀ := by sorry
