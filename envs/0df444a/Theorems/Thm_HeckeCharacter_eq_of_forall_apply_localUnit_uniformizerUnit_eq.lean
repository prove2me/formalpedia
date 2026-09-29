-- Prove2me | Theorems.Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq
-- name    : HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/62859a6b-1473-507d-81d0-ff428ddcdfec
-- title:
--   Idele class characters determined by almost all uniformizer values
-- statement:
--   Let $K$ be a number field, and let $\chi_1,\chi_2\colon \mathbb{A}_K^{\times}\to\mathbb{C}^{\times}$ be monoid homomorphisms on the units of the adele ring of $K$ (realised as the product of the infinite adeles and the finite adeles, so that an adele $x$ has components $x.1$ and $x.2$). Assume each $\chi_j$ is an idele class character in the sense that it is trivial on the image of $K^{\times}$ under the diagonal map $K\to\mathbb{A}_K$, that each $\chi_j$ is continuous, and that integral ideals $\mathfrak{f}_1,\mathfrak{f}_2$ of $\mathcal{O}_K$ are given (unrelated to one another) such that $\chi_j$ admits $\mathfrak{f}_j$ as a modulus: whenever a unit $u$ of $\mathbb{A}_K$ has infinite component equal to $1$ and satisfies, at every finite place $v$, both $|u_v|_v = 1$ and $|u_v-1|_v \le \exp(-n_v(\mathfrak{f}_j))$, where $n_v(\mathfrak{f}_j)$ is the multiplicity of $v$ in the factorisation of $\mathfrak{f}_j$, then $\chi_j(u)=1$. For a finite place $v$ write $\varpi_v$ for the idele whose component at $v$ is the unit of $K_v$ given by the chosen uniformizer of $v$ and whose components at all other finite places and at the infinite component are $1$. If there is a finite set $S$ of finite places with $\chi_1(\varpi_v)=\chi_2(\varpi_v)$ for all $v\notin S$, then $\chi_1=\chi_2$.
--
--   This is the standard uniqueness statement for Hecke characters in adelic form: a continuous idele class character with a modulus is determined by its values at the uniformizer ideles of all but finitely many finite places, the point being that $K^{\times}$, the congruence subgroup attached to a modulus and the remaining uniformizer ideles generate a dense subgroup of the idele group. It is used in the project to identify central characters of adelic automorphic realisations that agree away from a finite set of places, and thence in comparisons of newform spans.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

theorem HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq
    (K : Type*) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ₁ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₁)
    (hχ₂ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₂)
    (hc₁ : Continuous χ₁)
    (hc₂ : Continuous χ₂)
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      χ₁ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))
        = χ₂ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))) :
    χ₁ = χ₂ := by sorry
