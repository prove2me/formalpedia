-- Prove2me | Theorems.Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
-- name    : M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/5d5d232c-a288-517f-ab25-8eaaec6ea2e6
-- title:
--   Ramification theorem: inertia lies in the image of local units
-- statement:
--   Let $E$ and $F$ be number fields with $F/E$ Galois and $\mathrm{Gal}(F/E) = (F \simeq_{\mathrm{alg}[E]} F)$ commutative. Let $\mathfrak f$ be an ideal of $\mathcal O_E$ that is an admissible modulus of degree $[F:E]$, i.e. $\mathfrak f \neq 0$ and for every finite place $v$ of $E$ at which the inertia subgroup of `primeAbove E F v` in $\mathrm{Gal}(F/E)$ is nontrivial, $v^{\,\mathtt{admissibleExpOfDegree}\,E\,[F:E]\,v}$ divides $\mathfrak f$. Let $r$ be a group homomorphism from the idèles $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ such that: the principal idèles (the image of $E^\times$) lie in $\ker r$; $\ker r$ is the join of the principal idèles with the range of the idelic norm $(\mathbb A_F)^\times \to (\mathbb A_E)^\times$ attached to the base change `genuineBaseChange E F`; $r$ is surjective; and for every idèle $u$ satisfying `IsAdjuster E 𝔣 u 1` — at each $v \mid \mathfrak f$ the finite component $u_v$ has valuation $1$ and $|u_v - 1| \le \exp(-\mathrm{ord}_v(\mathfrak f))$, and $u$ is positive at every real embedding — one has $r(u) = \prod^{\mathrm f}_v \mathtt{artinFrob}\,E\,F\,v^{\,\mathrm{ord}_v(u)}$, the Frobenius at a chosen prime above $v$ raised to the $v$-adic order of the finite part of $u$. Let $v$ be a finite place of $E$ and $w$ a finite place of $F$ lying over $v$. Then the inertia subgroup of $w$ in $\mathrm{Gal}(F/E)$ is contained in the image under $r$ of `unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ)`, the intersection of the idèles whose finite component at $v$ is integral with integral inverse with the subgroup `idelesTrivialOn (𝓞 E) E ({v}ᶜ)`, which constrains the components at the places other than $v$.
--
--   This is one inclusion of the ramification theorem of global class field theory: the idelic Artin map carries the local units at $v$ onto the inertia group at a place $w$ above $v$, the reverse inclusion being the Frobenius property of $r$. It is used to produce local units at a ramified place outside the product of principal idèles and norms, and in the computation of conductor exponents of Artin symbols.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap.lean

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
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open M4aHerbrand
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    w.asIdeal.inertia (F ≃ₐ[E] F)
      ≤ (unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r := by sorry
