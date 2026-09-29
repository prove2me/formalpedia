-- Prove2me | Theorems.Thm_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
-- name    : Ideal.exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/3be04478-93e3-5335-a5c1-a31e84eb8ae4
-- title:
--   Clearing denominators: finitely generated ideals agreeing locally at 𝔭
-- statement:
--   Let $S$ and $B$ be commutative rings, $\varphi\colon S\to B$ a ring homomorphism, and $\mathfrak p\subset S$ a prime ideal. Let $B_{\mathfrak p}$ be a commutative ring carrying a $B$-algebra structure which makes it a localisation of $B$ at the submonoid $\varphi(S\setminus\mathfrak p)$, the image under $\varphi$ (as a monoid homomorphism) of the multiplicative complement $S\setminus\mathfrak p$. Let $J_1,J_2$ be ideals of $B$, both finitely generated, whose extensions along the structure map $B\to B_{\mathfrak p}$ agree, i.e. $J_1B_{\mathfrak p}=J_2B_{\mathfrak p}$ as ideals of $B_{\mathfrak p}$ (the images under `Ideal.map`). The assertion is that there exists $g\in S$ with $g\notin\mathfrak p$ such that for every commutative ring $B'$ with a $B$-algebra structure exhibiting $B'$ as a localisation of $B$ away from $\varphi(g)$, that is at the submonoid of powers of $\varphi(g)$, the extensions of $J_1$ and $J_2$ along $B\to B'$ coincide: $J_1B'=J_2B'$. The single element $g$ works simultaneously for all such $B'$, the quantification over $B'$ sitting inside the existential.
--
--   This is the standard clearing-of-denominators (spreading-out) statement: an equality of finitely generated ideals that holds after localising at a prime already holds after inverting a single element outside that prime, with the inverted element taken in the base ring $S$ via $\varphi$. It is used in the geometric step [`AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper`](thm.html#AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper), where a condition verified at a point of the base must be propagated to an open neighbourhood.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
    {S B : Type} [CommRing S] [CommRing B] (φ : S →+* B) (𝔭 : Ideal S) [𝔭.IsPrime]
    (Bₚ : Type) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bₚ]
    (J₁ J₂ : Ideal B) (h₁ : J₁.FG) (h₂ : J₂.FG)
    (h : J₁.map (algebraMap B Bₚ) = J₂.map (algebraMap B Bₚ)) :
    ∃ g : S, g ∉ 𝔭 ∧
      ∀ (B' : Type) [CommRing B'] [Algebra B B'] [IsLocalization.Away (φ g) B'],
        J₁.map (algebraMap B B') = J₂.map (algebraMap B B') := by sorry
