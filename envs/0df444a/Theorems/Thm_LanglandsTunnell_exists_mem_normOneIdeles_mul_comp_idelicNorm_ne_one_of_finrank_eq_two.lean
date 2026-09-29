-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one_of_finrank_eq_two
-- name    : LanglandsTunnell.exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/f606b6e0-1297-5c54-b63c-0a033f4f4a27
-- title:
--   Non-triviality of ξ·(χ∘ N) on the norm-one ideles
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra of degree $[M:E]=2$, and let $\xi\colon(\mathbb{A}_M)^\times\to\mathbb{C}^\times$ be a monoid homomorphism on the units of the adele ring of $M$ which is a finite-order Hecke character, i.e. trivial on the image of $M^\times$, continuous, and of finite order. Let $S_0$ be a finite set of maximal ideals of $\mathcal{O}_M$ such that for every prime $w'\notin S_0$ the character $\xi$ is unramified at $w'$, in the sense that its local component at $w'$ takes the value $1$ on every unit $t$ of the completion $M_{w'}$ with both $t$ and $t^{-1}$ in the valuation ring. Assume further that there are two distinct primes $w'\neq w''$ of $\mathcal{O}_M$, both outside $S_0$, lying over the same prime of $\mathcal{O}_E$, with $\xi(\varpi_{w'})\neq\xi(\varpi_{w''})$, where $\varpi_w$ denotes the idele that is a uniformizer at $w$ and $1$ at all other places, infinite places included. Finally let $\chi\colon(\mathbb{A}_E)^\times\to\mathbb{C}^\times$ be continuous with $\lVert\chi(x)\rVert=1$ for all $x$. Then there is an idele $x$ in the kernel of the Haar character of $\mathbb{A}_M$ (the norm-one ideles) with $\xi(x)\,\chi(N(x))\neq 1$, where $N$ is the idelic norm $(\mathbb{A}_M)^\times\to(\mathbb{A}_E)^\times$ induced by the algebra norm for the base change $\mathbb{A}_E\otimes_E M\cong\mathbb{A}_M$.
--
--   This is the non-degeneracy step in the construction of the automorphic form attached by Hecke's and Jacquet–Langlands' theory to a finite-order character $\xi$ of a quadratic extension: the hypothesis that $\xi$ separates two primes above one prime of $E$ prevents $\xi$ from agreeing with a unitary character of $E$ composed with the norm, even after restriction to the norm-one ideles, which is what makes the associated theta series cuspidal. It is used in assembling the pinned twisted datum induced from a finite-order Hecke character of a quadratic extension, in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
  M4aHerbrand.GenuineDescent

theorem LanglandsTunnell.exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hcχ : Continuous χ) (huχ : IsUnitaryChar (𝓞 E) E χ) :
    ∃ x ∈ normOneIdeles M, (ξ * χ.comp (genuineBaseChange E M).idelicNorm) x ≠ 1 := by sorry
