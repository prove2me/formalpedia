-- Prove2me | Theorems.Thm_NumberField_exists_isGaussDatum
-- name    : NumberField.exists_isGaussDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/bd8c5572-a39c-5aee-9de8-aa8a03c5fc44
-- title:
--   Existence of a Gauss datum for a narrow ray class character
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $\mathfrak{f}$ be an ideal of $\mathcal{O}_K$ with $\mathfrak{f}\neq 0$, and let $\chi$ be a homomorphism from the narrow ray class group $\mathrm{NarrowRayClassGroup}\ K\ \mathfrak{f}$ — the quotient of the group `coprimeToModulus K 𝔣` of invertible fractional ideals whose `FractionalIdeal.count` at every height-one prime $v$ of $\mathcal{O}_K$ dividing $\mathfrak{f}$ is $0$, by the subgroup induced by `narrowRaySubgroup K 𝔣` — into the multiplicative monoid $\mathbb{C}$. The assertion is that there exists $y\in K$ satisfying the predicate [`M4aP2.IsGaussDatum K 𝔣 χ y`](def/NumberField_RayCharacterData.html#L50), that is: $y\neq 0$; for every $\alpha\in\mathcal{O}_K$ lying in $\mathfrak{f}$ the trace $\mathrm{Tr}_{K/\mathbb{Q}}(\alpha y)$ lies in the image of $\mathbb{Z}\to\mathbb{Q}$, i.e. is a rational integer; and the value of `chiIdeal K 𝔣 χ` at the fractional ideal $(y)\,\mathfrak{f}\,\mathfrak{d}$, where $\mathfrak{d}=$ `differentIdeal ℤ (𝓞 K)`, is non-zero. By the definition of `chiIdeal`, this last condition says that $(y)\,\mathfrak{f}\,\mathfrak{d}$ is non-zero, that as a unit it lies in `coprimeToModulus K 𝔣` (its count vanishes at all primes dividing $\mathfrak{f}$), and that $\chi$ does not vanish on its narrow ray class.
--
--   This is the existence of the auxiliary element $y\in(\mathfrak{f}\mathfrak{d})^{-1}$ with $(y)\mathfrak{f}\mathfrak{d}$ coprime to $\mathfrak{f}$ which enters Hecke's Gauss sum $\tau(\chi,y)=\sum_{x\bmod\mathfrak f}\chi(x)e^{2\pi i\,\mathrm{Tr}(xy)}$ attached to a narrow ray class character, and thereby the root number in the functional equation of $L(s,\chi)$. It is used by [`NumberField.exists_completedRayL_functionalEquation_of_primitive`](thm.html#NumberField.exists_completedRayL_functionalEquation_of_primitive), where the functional equation of the completed narrow ray class $L$-function is formulated in terms of such a datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isGaussDatum.lean

import Mathlib
import Definitions.Def_NumberField_RayCharacterData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField Deep.NTSupply

theorem NumberField.exists_isGaussDatum
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ y : K, M4aP2.IsGaussDatum K 𝔣 χ y := by sorry
