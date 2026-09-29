-- Prove2me | Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
-- name    : NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3c3baab5-f01d-579f-ac7a-14d1324362b7
-- title:
--   Idelic Artin map for an admissible modulus of the degree
-- statement:
--   Let $F/E$ be a Galois extension of number fields whose Galois group $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$ is commutative, and let $\mathfrak f$ be an ideal of $\mathcal O_E$ which is an admissible modulus for the degree $n := [F:E]$, that is: $\mathfrak f \neq 0$, and for every finite place $v$ of $E$ whose chosen prime `primeAbove E F v` of $\mathcal O_F$ has non-trivial inertia subgroup in $\mathrm{Gal}(F/E)$, the power $v^{\,e_v}$ divides $\mathfrak f$, where $e_v = 1 + \sum_{p \mid n} (\mathrm{ord}_p(n)+1)\,e(p\mathbb Z, v)$. Then there exists a group homomorphism $r$ from the idèle group $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ such that: the subgroup of principal idèles, the image of $E^\times$ under the structure map, lies in $\ker r$; indeed $\ker r$ is exactly the join of the principal idèles with the image of the idelic norm $(\mathbb A_F)^\times \to (\mathbb A_E)^\times$ attached to the base change `genuineBaseChange E F` (the map $\mathrm{Units}$ applied to the algebra norm of $\mathbb A_F$ over $\mathbb A_E$ along the comparison isomorphism $\mathbb A_E \otimes_E F \cong \mathbb A_F$); $r$ is surjective; and for every idèle $u$ that is $1$-adjusted at level $\mathfrak f$, meaning that at each finite $v \mid \mathfrak f$ the finite component $u_v$ has valuation $1$ and $|u_v - 1| \le \exp(-\mathrm{ord}_v(\mathfrak f))$, and $u$ is positive at every real embedding $\tau : E \to \mathbb R$ in the sense of `archSign`, one has $$r(u) = \prod_{v}^{\mathrm f} \big(\mathrm{artinFrob}\,E\,F\,v\big)^{\mathrm{ord}_v(u_v)},$$ a finite product over the finite places $v$ of $E$ of the arithmetic Frobenius at `primeAbove E F v` raised to $\mathrm{ord}_v(u_v) = -\log |u_v|_v$.
--
--   This is the idelic global reciprocity law (Artin reciprocity in idelic form) for an abelian extension of number fields, at a modulus admissible for the degree, packaged so that the reciprocity map is trivial on principal idèles, has the norm class group as kernel, is surjective, and is computed by a Frobenius product on idèles adjusted at the modulus. It is the input for the construction of Hecke characters attached to abelian extensions and for the Artin $L$-function computations used downstream in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

theorem NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣) :
    ∃ r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F),
      principalIdeles (𝓞 E) E ≤ r.ker ∧
      r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range ∧
      Function.Surjective r ∧
      ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
        r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v := by sorry
