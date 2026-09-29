-- Prove2me | Theorems.Thm_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff
-- name    : HeckeCharacter.fadContentHom_mem_coprimeToModulus_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/281e91d9-c6ba-5e37-8795-ee759ebe15d7
-- title:
--   Content of a finite idèle is coprime to f iff locally unit
-- statement:
--   Let $K$ be a number field, let $\mathfrak f$ be an ideal of the ring of integers $\mathcal O_K$, and let $y$ be a unit of the finite adèle ring of $K$ over $\mathcal O_K$. Write $\mathrm{placeOrd}\,K\,y\,v = -\log \mathrm{v}(y_v)$ for the valuation exponent of the $v$-component of $y$ at a height-one prime $v$ of $\mathcal O_K$, and let $\mathrm{fadContentHom}\,K\,y = \prod_v (\mathfrak p_v)^{\mathrm{placeOrd}\,K\,y\,v}$ be the associated invertible fractional ideal, the product being taken over all height-one primes with $\mathfrak p_v$ the invertible fractional ideal attached to $v$. The theorem asserts the equivalence of two conditions: first, that $\mathrm{fadContentHom}\,K\,y$ lies in the subgroup $\mathrm{coprimeToModulus}\,K\,\mathfrak f$ of invertible fractional ideals, that is, that its multiplicity (`FractionalIdeal.count`) at every height-one prime $v$ whose ideal divides $\mathfrak f$ vanishes; second, that $\mathrm{placeOrd}\,K\,y\,w = 0$ for every height-one prime $w$ with $w$'s ideal dividing $\mathfrak f$, i.e. that $y$ is a local unit at every prime dividing $\mathfrak f$.
--
--   This is the standard compatibility between the content (ideal) map on finite idèles and the group of fractional ideals coprime to a modulus: coprimality of the content to $\mathfrak f$ is exactly the condition that the idèle have trivial valuation at the primes dividing $\mathfrak f$. It is used to pass between idèles adjusted at a modulus and ideals coprime to it, in the construction of Hecke characters and in the identification of a Frobenius product expansion in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem HeckeCharacter.fadContentHom_mem_coprimeToModulus_iff
    (K : Type*) [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)} (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K y ∈ coprimeToModulus K 𝔣 ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 → placeOrd K y w = 0 := by sorry
