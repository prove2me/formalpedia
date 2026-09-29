-- Prove2me | Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
-- name    : NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/7e4fe325-e731-5de8-a0b9-17cbe3a1750d
-- title:
--   Idele character unramified outside S kills units away from S
-- statement:
--   Let $F$ be a number field, let $\chi \colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be a continuous group homomorphism on the units of the adele ring of $\mathcal{O}_F$ in $F$ (the adele ring being the product of the infinite adeles with the finite adeles, so that an adele has an archimedean component and a component at each $v$ in the height one spectrum of $\mathcal{O}_F$), and let $S$ be a finite set of height one primes of $\mathcal{O}_F$. Assume that for every $v \notin S$ the character $\chi$ is unramified at $v$ in the sense of `IsUnramifiedCharAt`: for every unit $t$ of the completion $F_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring $\mathcal{O}_v$, the local character `localChar` at $v$ — namely $\chi$ composed with the embedding of $F_v^\times$ into the finite idele units at the single place $v$ followed by the inclusion of the finite adeles into the adeles — takes the value $1$ at $t$. The conclusion is that $\chi(u) = 1$ for every adelic unit $u$ whose archimedean component is $1$, whose component at each $v \in S$ is $1$, and whose finite part, the image of $u$ under `finitePartUnits` (the unit map of the projection to the finite adeles), lies in `unitIdeles`, i.e. both it and its inverse have all components in the respective rings $\mathcal{O}_v$.
--
--   This is the standard statement that a continuous character of the idele group which is unramified outside a finite set $S$ of finite places is trivial on the compact subgroup $\prod_{v \notin S} \mathcal{O}_v^\times$, the passage from triviality on each single-place unit group to triviality on the whole product. It is used as the unramifiedness input in the Euler-product packaging of global zeta integrals and in the bad-set bookkeeping for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdeleRing IsDedekindDomain

theorem NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) :
    ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      χ u = 1 := by sorry
