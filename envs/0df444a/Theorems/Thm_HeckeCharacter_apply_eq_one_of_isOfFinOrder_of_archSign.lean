-- Prove2me | Theorems.Thm_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign
-- name    : HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ca21e247-f0e7-5da1-8698-fe82d47dda95
-- title:
--   Finite-order idèle characters kill totally positive infinite idèles
-- statement:
--   Let $K$ be a number field and $M$ a commutative monoid, and let $\eta$ be a monoid homomorphism from the unit group $(\mathbb{A}_K)^\times$ of the adèle ring of $K$ (realised as the product of the infinite adèle ring with the finite adèle ring of $\mathcal{O}_K$) to $M$, assumed to be of finite order as an element of the monoid of such homomorphisms under pointwise multiplication. Let $u$ be a unit of the adèle ring satisfying two conditions: its finite component, the second coordinate of $u$ in $\mathbb{A}_K$, equals $1$; and for every ring homomorphism $\tau : K \to \mathbb{R}$ the predicate [`HeckeCharacter.archSign`](def/LanglandsTunnell_ArtinCoreCTM.html#L182) holds at $\tau$ and $u$, that is, the real number obtained by taking the component of the infinite part of $u$ at the infinite place determined by $\tau$ and transporting it through the isomorphism of that real completion with $\mathbb{R}$ is strictly positive. The conclusion is $\eta(u) = 1$. No continuity or measurability hypothesis on $\eta$ is imposed, and $M$ is an arbitrary commutative monoid.
--
--   This is the triviality clause on the totally positive archimedean part used in handling Hecke characters of $K$: it is what makes the value of a finite-order idèle character depend only on the ray class of an idèle. It is used in the computation of ray symbols on uniformiser idèles and on $-1$ at the archimedean places, and in the construction of an odd admissible twist in the converse direction of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommMonoid M]
    (η : (AdeleRing (𝓞 K) K)ˣ →* M) (hη : IsOfFinOrder η)
    (u : (AdeleRing (𝓞 K) K)ˣ) (hfin : (u : AdeleRing (𝓞 K) K).2 = 1)
    (hpos : ∀ τ : K →+* ℝ, HeckeCharacter.archSign K τ u) :
    η u = 1 := by sorry
