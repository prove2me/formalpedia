-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom
-- name    : LanglandsTunnell.P2.Artin.artinSymbol_fadContentHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/467ca9a8-cf67-5765-a948-aad81af5fef0
-- title:
--   Artin symbol of an idèle's content as a Frobenius product
-- statement:
--   Let $K$ and $M$ be number fields with $M$ a Galois extension of $K$ whose Galois group $M \simeq_{\mathrm{alg}[K]} M$ is commutative, let $\mathfrak f$ be an ideal of $\mathcal O_K$, and let $u$ be a unit of the adèle ring of $K$. Write $\operatorname{projFin} K u$ for the finite-adelic component of $u$, obtained as the second coordinate under the identification of the units of the adèle ring with the product of the units of the infinite and the finite adèle rings, and for a finite place $v$ set $\mathrm{placeOrd}\,K\,(\operatorname{projFin} K u)\,v = -\log |(\operatorname{projFin} K u)_v|_v$, the negative of the `WithZero` logarithm of the $v$-adic valuation of the $v$-component. Let $\mathrm{fadContentHom}$ be the homomorphism sending a finite idèle $y$ to the unit fractional ideal $\prod_v^{\mathrm f} (v)^{\mathrm{placeOrd}\,K\,y\,v}$ of $K$. Assume that the content $\mathrm{fadContentHom}\,K\,(\operatorname{projFin} K u)$ lies in the subgroup `coprimeToModulus K 𝔣` of those unit fractional ideals whose $v$-adic count vanishes at every finite place $v$ with $v.\mathrm{asIdeal} \mid \mathfrak f$. Then the Artin symbol `artinSymbol K M 𝔣`, i.e. the ray symbol homomorphism on that subgroup determined by the prime values $v \mapsto \mathrm{artinFrob}\,K\,M\,v$ (the arithmetic Frobenius at a chosen prime of $\mathcal O_M$ above $v$), evaluated at this content equals $\prod_v^{\mathrm f} (\mathrm{artinFrob}\,K\,M\,v)^{\mathrm{placeOrd}\,K\,(\operatorname{projFin} K u)\,v}$, a finitely supported product in the Galois group.
--
--   This is the compatibility formula by which the idelic Artin reciprocity map is computed on idèles prime to the modulus: the Artin symbol of the ideal content of an idèle is the product of local Frobenius elements raised to the local orders. It is used in the construction of the idelic Artin map for a number field, namely by [`LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd`](thm.html#LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd) and the two existence statements [`NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_dvd_twentyFour`](thm.html#NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_dvd_twentyFour) and [`NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank`](thm.html#NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem LanglandsTunnell.P2.Artin.artinSymbol_fadContentHom
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    [IsMulCommutative (M ≃ₐ[K] M)] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣) :
    artinSymbol K M 𝔣 ⟨fadContentHom K (projFin K u), hu⟩ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K M v ^ placeOrd K (projFin K u) v := by sorry
