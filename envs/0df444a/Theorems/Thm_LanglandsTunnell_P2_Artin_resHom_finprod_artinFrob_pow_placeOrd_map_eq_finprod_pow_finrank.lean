-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank
-- name    : LanglandsTunnell.P2.Artin.resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1f99cbba-1898-5962-9dc9-1a16a4578335
-- title:
--   Restriction of the Frobenius idèle symbol under base change
-- statement:
--   Let $E$, $F$, $N$, $L'$ be number fields equipped with $E$-algebra structures on $F$, $N$, $L'$ together with $F \to N$ and $L' \to N$ forming scalar towers $E \subseteq F \subseteq N$ and $E \subseteq L' \subseteq N$, and assume $N/F$ is Galois with abelian group $\mathrm{Gal}(N/F)$ and $L'/E$ is Galois with abelian group $\mathrm{Gal}(L'/E)$. Let $u$ be a unit of the adèle ring of $E$, and write $\mathrm{ord}_v(u) := -\log \lvert u_v \rvert_v$ for the integer `placeOrd` attached to the finite-adèle component of $u$ at a height-one prime $v$ of $\mathcal{O}_E$ (the negative of the `WithZero` logarithm of its valuation). Assume that for every $v$ with $\mathrm{ord}_v(u) \neq 0$, every maximal ideal $Q$ of $\mathcal{O}_{L'}$ with $Q \cap \mathcal{O}_E = v$ has trivial inertia subgroup in $\mathrm{Gal}(L'/E)$. Then applying the homomorphism $\mathrm{Gal}(N/F) \to \mathrm{Gal}(L'/E)$ given by restriction of scalars to $E$ followed by restriction to the normal subextension $L'$, to the finite product $\prod^{\mathrm{f}}_{w} \mathrm{Frob}_w(N/F)^{\,\mathrm{ord}_w(\beta u)}$ over height-one primes $w$ of $\mathcal{O}_F$ — where $\beta$ is the ring homomorphism $\mathbb{A}_E \to \mathbb{A}_F$ of the adèle base change `genuineBaseChange` and $\mathrm{Frob}_w$ is the arithmetic Frobenius at the chosen prime of $N$ above $w$ — yields $\bigl(\prod^{\mathrm{f}}_{v} \mathrm{Frob}_v(L'/E)^{\,\mathrm{ord}_v(u)}\bigr)^{[F:E]}$, the product over height-one primes $v$ of $\mathcal{O}_E$ raised to the $E$-rank of $F$.
--
--   This is the functoriality of the Artin (reciprocity) symbol of an idèle under base change: restricting the Frobenius product of the base-changed idèle $\beta u$ to an abelian layer $L'/E$ below returns the $[F:E]$-th power of the Frobenius product of $u$ itself, the three ingredients being $\mathrm{ord}_w(\beta u) = e(w\mid v)\,\mathrm{ord}_v(u)$, the relation $\mathrm{res}\,\mathrm{Frob}_w(N/F) = \mathrm{Frob}_v(L'/E)^{f(w\mid v)}$ at places unramified in $L'$, and $\sum_{w \mid v} e(w\mid v) f(w\mid v) = [F:E]$. It feeds the norm-compatibility statement [`NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm`](thm.html#NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm) used in the class-field-theoretic input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem LanglandsTunnell.P2.Artin.resHom_finprod_artinFrob_pow_placeOrd_map_eq_finprod_pow_finrank
    (E F N L' : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Field L'] [NumberField L']
    [Algebra E F] [Algebra E N] [Algebra F N] [Algebra E L'] [Algebra L' N]
    [IsScalarTower E F N] [IsScalarTower E L' N]
    [IsGalois F N] [IsMulCommutative (N ≃ₐ[F] N)] [IsGalois E L'] [IsMulCommutative (L' ≃ₐ[E] L')]
    (u : (AdeleRing (𝓞 E) E)ˣ)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 E), placeOrd E (projFin E u) v ≠ 0 →
      ∀ Q : Ideal (𝓞 L'), Q.IsMaximal → Q.under (𝓞 E) = v.asIdeal → Q.inertia (L' ≃ₐ[E] L') = ⊥) :
    resHom E L' F N (∏ᶠ w : HeightOneSpectrum (𝓞 F),
        artinFrob F N w ^ placeOrd F (projFin F (Units.map (genuineBaseChange E F).β.toMonoidHom u)) w) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E L' v ^ placeOrd E (projFin E u) v) ^ Module.finrank E F := by sorry
