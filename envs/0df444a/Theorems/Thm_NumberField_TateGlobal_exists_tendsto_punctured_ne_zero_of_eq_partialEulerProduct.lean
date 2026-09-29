-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
-- name    : NumberField.TateGlobal.exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/8af400ba-5cca-5ce3-933a-4cabf7f2743c
-- title:
--   Non-vanishing of partial Hecke L-functions on Re s=1
-- statement:
--   Let $F$ be a number field, $S$ a finite set of maximal ideals of $\mathcal{O}_F$, and let $\varpi$ assign to each $v$ in the height-one spectrum of $\mathcal{O}_F$ a unit $\varpi_v$ of the completion $F_v$ whose valuation is $\mathrm{ofAdd}(-1)$, i.e. a uniformiser. Let $\chi$ be a continuous homomorphism from the units of the adele ring of $F$ to $\mathbb{C}^\times$ which is unitary, in the sense that $\|\chi(x)\|=1$ for every idele unit $x$, and an idele class character, in the sense that $\chi$ is trivial on the image of $F^\times$. Let $L:\mathbb{C}\to\mathbb{C}$ be meromorphic on all of $\mathbb{C}$ and satisfy, for every $s$ with $\operatorname{Re} s>1$, $$L(s)=\Bigl(\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)\,(\mathrm{N}v)^{-s}\bigr)\Bigr)^{-1},$$ the inverse of the (unconditional) infinite product over the primes outside $S$, where $\mathrm{N}v$ is the absolute norm of $v$ and $\chi_v(\varpi_v)$ is the value of $\chi$ at the idele whose component at $v$ is $\varpi_v$ and whose components elsewhere, at the finite and at the infinite places, are $1$. Let $t$ be a real number such that the character $x\mapsto\chi(x)\,\|x\|^{it}$, with $\|x\|$ the module of $x$ given by the distributive Haar character of the adele ring, is not the trivial character. Then there is a non-zero $c\in\mathbb{C}$ such that $L(s)\to c$ as $s\to 1+it$ with $s\neq 1+it$.
--
--   This is the classical non-vanishing of Hecke $L$-functions on the line $\operatorname{Re} s=1$, in the form of Hadamard and de la Vallée Poussin, stated as a non-zero punctured limit at $1+it$ because a meromorphic function's value at a single point is not pinned down by its values elsewhere; the excluded case $\chi\cdot\|\cdot\|^{it}=1$ is exactly the one where the product is a shifted Dedekind zeta function with a pole at $1+it$. It feeds the lower bounds for $|L|$ near the line $\operatorname{Re} s = 1$ used in the analytic theory of automorphic $L$-functions built on Tate's global theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct.lean

import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ)
    (L : ℂ → ℂ) (hL : MeromorphicOn L Set.univ)
    (hLE : ∀ s : ℂ, 1 < s.re →
      L s = (∏' v : {v // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (t : ℝ) (ht : χ * normPowChar F t ≠ 1) :
    ∃ c : ℂ, c ≠ 0 ∧
      Filter.Tendsto L (nhdsWithin (1 + t * Complex.I) {1 + t * Complex.I}ᶜ) (nhds c) := by sorry
