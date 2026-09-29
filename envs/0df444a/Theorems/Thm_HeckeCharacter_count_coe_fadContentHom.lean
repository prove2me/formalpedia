-- Prove2me | Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
-- name    : HeckeCharacter.count_coe_fadContentHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f142952a-9fe6-5d79-ac04-782aa1f61c33
-- title:
--   Multiplicity at w of the content of a finite idèle
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, let $y$ be a unit of the finite adèle ring $\mathbb A_{K,\mathrm{fin}}$ of $K$, and let $w$ be a height-one prime of $\mathcal O_K$. For a unit $u$ of the finite adèle ring and a height-one prime $v$, `placeOrd K u v` is the integer $-\log$ of the (multiplicatively written, $\mathbb Z$-valued with zero) valuation of the $v$-component of $u$, i.e. the order of vanishing $\mathrm{ord}_v(u_v)$; and `fadContentHom K u` is the unit fractional ideal $\prod_v \mathfrak p_v^{\,\mathrm{ord}_v(u_v)}$, the finitely-supported product over all height-one primes $v$ of the $\mathrm{placeOrd}$-th power of `primeUnit K v`, the invertible fractional ideal attached to $v.\mathrm{asIdeal}$ (nonzero because $v \ne 0$), this assignment being a monoid homomorphism from $(\mathbb A_{K,\mathrm{fin}})^\times$ to the group of invertible fractional ideals of $\mathcal O_K$ in $K$. The theorem asserts that the multiplicity `FractionalIdeal.count K w` at $w$ of the fractional ideal underlying `fadContentHom K y` equals `placeOrd K y w`, that is, the content map recovers at $w$ exactly the valuation of the $w$-component of $y$.
--
--   This is the compatibility of the content (or ideal) map on finite idèles with the $w$-adic multiplicity function: the exponent vector of the content of an idèle is its vector of valuations at the finite places. It is the basic computational tool used downstream when identifying the image of `fadContentHom` on local subgroups, in particular in the statements about coprimality to a modulus and about adjusting an idèle so that its content has prescribed behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_count_coe_fadContentHom.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem HeckeCharacter.count_coe_fadContentHom
    (K : Type*) [Field K] [NumberField K]
    (y : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
      ((fadContentHom K y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = placeOrd K y w := by sorry
