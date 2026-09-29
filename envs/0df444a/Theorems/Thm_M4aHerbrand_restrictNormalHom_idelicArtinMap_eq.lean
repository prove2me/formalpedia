-- Prove2me | Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
-- name    : M4aHerbrand.restrictNormalHom_idelicArtinMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/529da52f-162a-59b0-9e2d-d325541c98b7
-- title:
--   Compatibility of idelic Artin maps with restriction to a subextension
-- statement:
--   Let $E$, $F$, $L$ be number fields with $F/E$ Galois and $\mathrm{Gal}(F/E)$ commutative, and with $L$ an intermediate layer: $L$ is an $E$-algebra and $F$ an $L$-algebra forming a scalar tower over $E$, $L/E$ is Galois and $\mathrm{Gal}(L/E)$ is commutative. Let $\mathfrak f$ be an ideal of $\mathcal O_E$ admissible for the degree $[F:E]$ relative to $F$, that is $\mathfrak f\neq 0$ and, for every finite place $v$ of $E$ at which the chosen prime `primeAbove E F v` has nontrivial inertia subgroup in $\mathrm{Gal}(F/E)$, $v^{1+\sum_{p\mid [F:E]}(\mathrm{ord}_p[F:E]+1)\,e(p\mathbb Z,v)}$ divides $\mathfrak f$. Let $r$ be a monoid homomorphism from the idèle group $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ such that: the principal idèles, i.e. the image of $E^\times$, lie in $\ker r$; $\ker r$ is the join of the principal idèles with the range of the idelic norm $(\mathbb A_F)^\times\to(\mathbb A_E)^\times$ attached to `genuineBaseChange E F` (the units map of the algebra norm along the adelic base change); $r$ is surjective; and for every idèle $u$ satisfying `IsAdjuster E 𝔣 u 1` (each component at a place dividing $\mathfrak f$ has valuation $1$ and is congruent to $1$ to the precision given by the exponent of that place in $\mathfrak f$, and every real embedding gives a positive archimedean component), $r(u)=\prod_v^{\mathrm f} \mathrm{artinFrob}_{E,F}(v)^{\mathrm{ord}_v(u)}$, the finitary product over finite places $v$ of $E$ of the arithmetic Frobenius at `primeAbove E F v` raised to the exponent $-\log|u_v|_v$ of the finite part of $u$. Let $\mathfrak f_L$ and $r_L$ satisfy the same four conditions for $L/E$ and the degree $[L:E]$. Then for every idèle $x$ of $E$, the restriction of $r(x)$ to $L$ equals $r_L(x)$.
--
--   This is the functoriality of the global Artin map in towers: the idelic Artin map of $F/E$, composed with restriction of automorphisms to an intermediate abelian layer $L$, is the idelic Artin map of $L/E$. It is used in the analysis of the idelic Artin map at single places, for instance in the computations of local coordinates and of inertia membership of Frobenius products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.restrictNormalHom_idelicArtinMap_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]
    (L : Type) [Field L] [NumberField L] [Algebra E L] [Algebra L F] [IsScalarTower E L F] [IsGalois E L]
    [IsMulCommutative (L ≃ₐ[E] L)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (𝔣L : Ideal (𝓞 E)) (hadmL : NumberField.NormIndex.IsAdmissibleModulusOfDegree E L (Module.finrank E L) 𝔣L)
    (rL : (AdeleRing (𝓞 E) E)ˣ →* (L ≃ₐ[E] L))
    (hrL₁ : principalIdeles (𝓞 E) E ≤ rL.ker)
    (hrL₂ : rL.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E L).idelicNorm.range)
    (hrL₃ : Function.Surjective rL)
    (hrL₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣L u 1 →
      rL u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E L v ^ placeOrd E (projFin E u) v)
    (x : (AdeleRing (𝓞 E) E)ˣ) :
    AlgEquiv.restrictNormalHom L (r x) = rL x := by sorry
