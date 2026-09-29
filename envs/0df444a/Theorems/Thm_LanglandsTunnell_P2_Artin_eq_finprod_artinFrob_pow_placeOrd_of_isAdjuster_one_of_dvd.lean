-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd
-- name    : LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f70fe584-6b29-5cae-8097-f016589040c1
-- title:
--   Descent of the Frobenius product formula to level f
-- statement:
--   Let $E$ and $F$ be number fields with $F/E$ Galois and $\mathrm{Gal}(F/E) = (F \simeq_{\mathrm{alg}[E]} F)$ commutative, and let $\mathfrak f, \mathfrak f'$ be ideals of $\mathcal O_E$ with $\mathfrak f' \neq 0$, $\mathfrak f \mid \mathfrak f'$, and such that every height-one prime $v$ of $\mathcal O_E$ dividing $\mathfrak f'$ also divides $\mathfrak f$ (so the two ideals have the same prime support). Let $r$ be a monoid homomorphism from the unit group of the adèle ring of $E$ to $\mathrm{Gal}(F/E)$ whose kernel contains [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16), the image of $E^\times$ under the diagonal embedding, and also contains `unitIdeles E 𝔣`, the subgroup of idèles all of whose finite components have valuation $1$, which satisfy $|u_v - 1| \le \exp(-\operatorname{ord}_v(\mathfrak f))$ at every $v \mid \mathfrak f$, and which are positive at every real embedding $\tau : E \to \mathbb R$. Assume that for every idèle $u$ satisfying `IsAdjuster E 𝔣' u 1` — i.e. the finite component of $u$ has valuation $1$ and is congruent to $1$ to precision $\exp(-\operatorname{ord}_v(\mathfrak f'))$ at each $v \mid \mathfrak f'$, and $u$ has positive archimedean sign at every real embedding — one has $r(u) = \prod^{\mathrm f}_{v} \mathrm{artinFrob}_{E,F}(v)^{\,\mathrm{placeOrd}_E(\mathrm{projFin}_E u)(v)}$, the finitely supported product over height-one primes $v$ of the arithmetic Frobenius at the chosen prime of $\mathcal O_F$ above $v$ raised to $-\log$ of the valuation of the $v$-component of the finite part of $u$. Then the same formula for $r(u)$ holds for every idèle $u$ satisfying `IsAdjuster E 𝔣 u 1`.
--
--   This is the level-descent step in the construction of the idelic Artin map: a homomorphism on idèles trivial on principal idèles and on the level-$\mathfrak f$ unit idèles, and given by the Frobenius product on idèles adjusted at the deeper level $\mathfrak f'$, is given by that product already at level $\mathfrak f$. It feeds into [`NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_unitIdeles_le`](thm.html#NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_unitIdeles_le), which packages the existence, kernel and surjectivity of the idelic Artin map for an abelian extension of number fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem LanglandsTunnell.P2.Artin.eq_finprod_artinFrob_pow_placeOrd_of_isAdjuster_one_of_dvd
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 𝔣' : Ideal (𝓞 E)) (h𝔣' : 𝔣' ≠ ⊥) (hdvd : 𝔣 ∣ 𝔣')
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣' → v.asIdeal ∣ 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hprinc : M4aHerbrand.principalIdeles (𝓞 E) E ≤ r.ker) (hunits : unitIdeles E 𝔣 ≤ r.ker)
    (hiv' : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣' u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1) :
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v := by sorry
