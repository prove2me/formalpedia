-- Prove2me | Theorems.Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
-- name    : M4aHerbrand.map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/dadf3bbe-41e0-5719-a4b0-f478c1eba2e2
-- title:
--   Image of Eᵥ^×: decomposition group, of 𝒪ᵥ^×: inertia group
-- statement:
--   Let $F/E$ be an extension of number fields which is Galois with commutative Galois group $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$, and let $\mathfrak{f}$ be an ideal of $\mathcal{O}_E$ that is an admissible modulus for the degree $[F:E]$, that is, $\mathfrak{f} \neq 0$ and, for every finite place $v$ of $E$ at which the chosen prime `primeAbove E F v` of $\mathcal{O}_F$ has nontrivial inertia subgroup, $v^{e}$ divides $\mathfrak{f}$ with $e =$ `admissibleExpOfDegree E (Module.finrank E F) v`. Let $r$ be a homomorphism from the idèle group $(\mathbb{A}_E)^\times$ to $\mathrm{Gal}(F/E)$ subject to four conditions: the subgroup `principalIdeles` of idèles coming from $E^\times$ lies in $\ker r$; $\ker r$ is the join of `principalIdeles` and the range of the idelic norm attached to the base change `genuineBaseChange E F` of adèle rings from $E$ to $F$; $r$ is surjective; and for every idèle $u$ with `IsAdjuster E 𝔣 u 1` — so that the finite component of $u$ has valuation $1$ and is congruent to $1$ to the exact order of $\mathfrak{f}$ at each place dividing $\mathfrak{f}$, and $u$ is positive at every real embedding — one has $r(u) = \prod_{v}^{\mathrm{f}} \mathrm{Frob}_v^{\,\mathrm{ord}_v(u)}$, the finprod over finite places $v$ of `artinFrob E F v` raised to the power $-\log$ of the $v$-adic valuation of the finite part of $u$. Let $v$ be a finite place of $E$ and $w$ a finite place of $F$ lying under which $v$ sits, i.e. `w.under (𝓞 E) = v`. Then the image under $r$ of the subgroup of idèles whose infinite part is $1$ and whose finite component is $1$ at every place other than $v$ equals the decomposition subgroup of $w$ in $\mathrm{Gal}(F/E)$ ([`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of the valuation subring of the $w$-adic valuation of $F$), and the image of the further subgroup of those idèles whose component at $v$ is a unit (both it and its inverse being $v$-adically integral) equals the inertia subgroup `w.asIdeal.inertia (F ≃ₐ[E] F)`.
--
--   This is the local–global compatibility of the idelic reciprocity map at level zero: the local component at a finite place $v$, wild places included, has image the decomposition group of a place above $v$ and sends the local units onto the inertia group. It feeds the computation of the kernel of the local component (the local norm theorem) in [`M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq`](thm.html#M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq) and the identification of that component as a local reciprocity map in [`M4aHerbrand.isLocalReciprocityMap_of_idelicArtinMap_single`](thm.html#M4aHerbrand.isLocalReciprocityMap_of_idelicArtinMap_single).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open NumberField
open M4aHerbrand
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
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
    (idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r = NumberField.PlaceDecomp.decomp E F w ∧
    (unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r = w.asIdeal.inertia (F ≃ₐ[E] F) := by sorry
