-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
-- name    : NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/d6c33f28-ba05-5a31-b3bf-565781b77c44
-- title:
--   Meromorphic continuation of a partial Hecke Euler product
-- statement:
--   Let $F$ be a number field (with its ring of integers $\mathcal{O}_F$), let $S$ be a finite set of height-one primes of $\mathcal{O}_F$, i.e. of finite places of $F$, and let $\varpi$ assign to each finite place $v$ a unit $\varpi_v$ of the completion $F_v =$ `v.adicCompletion F`, subject to the hypothesis that the valuation of $\varpi_v$ equals $\mathrm{ofAdd}(-1)$, so that $\varpi_v$ is a uniformiser at $v$. Let $\chi : \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a monoid homomorphism on the units of the adele ring which is continuous, unitary in the sense that $\lVert \chi(x)\rVert = 1$ for every idele $x$, and an idele class character in the sense that $\chi$ kills the principal ideles, i.e. $\chi(\iota(u)) = 1$ for every $u \in F^\times$, where $\iota$ is induced by $F \to \mathbb{A}_F$. Then there exists a function $L : \mathbb{C} \to \mathbb{C}$, meromorphic on all of $\mathbb{C}$ (`MeromorphicOn L Set.univ`), such that for every $s$ with $\operatorname{Re} s > 1$ the value $L(s)$ is the inverse of the unconditional infinite product $\prod_{v \notin S}\bigl(1 - \chi_v(\varpi_v)\, N(v)^{-s}\bigr)$, taken over the finite places outside $S$, where $N(v)$ is the absolute norm of the prime ideal $v$ and $\chi_v$ is `localChar χ v`, the composite of $\chi$ with the embedding of $F_v^\times$ into $\mathbb{A}_F^\times$ placing $1$ at the infinite places and at all finite places other than $v$. Note that the inverse is taken of the whole product rather than factor by factor.
--
--   This is the analytic continuation of a Hecke $L$-function attached to a unitary idele class character, in the partial form in which the Euler factors at a finite set $S$ of places are dropped and, at the remaining places, the factor is formed from the value of $\chi_v$ on the chosen uniformiser (no unramifiedness being assumed). It feeds the constant-term and intertwining analysis of adelic Eisenstein series, and the accompanying statement that some function analytic near a neighbourhood multiplies the partial Euler product to $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        L s = (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by sorry
