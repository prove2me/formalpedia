-- Prove2me | Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
-- name    : M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/aa3c1585-ece2-5cc6-b02b-cf996186d7a3
-- title:
--   Idelic Artin map at one place: Frobenius modulo inertia
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois and $\mathrm{Gal}(F/E)$ commutative, and let $\mathfrak f$ be an ideal of $\mathcal O_E$ that is an admissible modulus for the degree $[F:E]$, i.e. $\mathfrak f \neq 0$ and for every finite place $v$ of $E$ at which the chosen prime `primeAbove E F v` of $\mathcal O_F$ has non-trivial inertia subgroup, $v^{\,e}$ divides $\mathfrak f$ for the exponent $e =$ `admissibleExpOfDegree E (Module.finrank E F) v`. Let $r$ be a homomorphism from the idèle group $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ such that: the principal idèles lie in $\ker r$; $\ker r$ is the join of the principal idèles with the image of the idèlic norm attached to the base change `genuineBaseChange E F`; $r$ is surjective; and for every idèle $u$ satisfying `IsAdjuster E 𝔣 u 1` (congruence to $1$ modulo $\mathfrak f$ at the places dividing $\mathfrak f$, together with positivity at all real embeddings), $r(u) = \prod_v^{\mathrm f} \mathrm{Frob}_v^{\,\mathrm{ord}_v(u)}$, the finite product of the Artin–Frobenius elements `artinFrob E F v` raised to `placeOrd E (projFin E u) v`. Let $v$ be a finite place of $E$, $a \in (E_v)^\times$, and $x$ an idèle whose archimedean part is $1$ and whose component at every finite place other than $v$ is $1$, with component $a$ at $v$. Let $w$ be a prime of $\mathcal O_F$ lying over $v$, and let $\varphi \in \mathrm{Gal}(F/E)$ be an arithmetic Frobenius element at $w$. Then $r(x)\,\varphi^{-n}$ lies in the inertia subgroup of $w$, where $n =$ `placeOrd E (projFin E x) v` is the normalised valuation $\mathrm{ord}_v(a)$.
--
--   This is the local Frobenius property of the global reciprocity map: on an idèle supported at a single finite place $v$, the idèlic Artin map agrees with $\mathrm{ord}_v$-th power of an arithmetic Frobenius at any prime $w \mid v$, up to inertia at $w$ (so exactly, when $v$ is unramified). It is used in the analysis of conductors of abelian Artin characters and in producing generators of $\mathrm{Gal}(F/E)$ from single-place idèles in the cyclic case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt.lean

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
open IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open NumberField
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (v : HeightOneSpectrum (𝓞 E)) (a : (v.adicCompletion E)ˣ) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv : finPart v x = a)

    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (φ : F ≃ₐ[E] F) (hφ : IsArithFrobAt (𝓞 E) φ w.asIdeal) :
    r x * (φ ^ placeOrd E (projFin E x) v)⁻¹ ∈ w.asIdeal.inertia (F ≃ₐ[E] F) := by sorry
