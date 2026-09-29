-- Prove2me | Theorems.Thm_M4aHerbrand_isLocalReciprocityMap_of_idelicArtinMap_single
-- name    : M4aHerbrand.isLocalReciprocityMap_of_idelicArtinMap_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e4c0ab26-a52a-57d3-ba8f-7e10ed1ca6cc
-- title:
--   Local components of the idelic Artin map are reciprocity maps
-- statement:
--   Let $E$ and $F$ be number fields with $F/E$ Galois and with commutative Galois group $\mathrm{Gal}(F/E)$. Let $\mathfrak f$ be an ideal of $\mathcal O_E$ which is an admissible modulus for the degree $[F:E]$, i.e. $\mathfrak f \neq 0$ and $v^{e}\mid\mathfrak f$, with $e$ the admissible exponent attached to the degree, for every finite place $v$ of $E$ whose chosen prime of $F$ above $v$ has nontrivial inertia. Let $r$ be a homomorphism from the idele group $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ such that: the principal ideles lie in $\ker r$; $\ker r$ is the join of the principal ideles and the image of the idelic norm $(\mathbb A_F)^\times \to (\mathbb A_E)^\times$ coming from `genuineBaseChange E F`; $r$ is surjective; and for every idele $u$ satisfying `IsAdjuster E 𝔣 u 1` (at each $v\mid\mathfrak f$ the finite component of $u$ has valuation $1$ and $u_v-1$ has valuation at most $\exp(-\mathrm{ord}_v\mathfrak f)$, and $u$ is positive at every real embedding) one has $r(u)=\prod^{\mathrm f}_{v}\,\mathrm{Frob}_v^{\,\mathrm{ord}_v(u)}$, the product over finite places of the Artin–Frobenius elements `artinFrob E F v` raised to the $v$-adic order of the finite part of $u$. Fix a finite place $v$ of $E$ and a finite place $w$ of $F$ with $w$ lying under $v$ over $\mathcal O_E$. Let $\iota_v\colon (E_v)^\times \to (\mathbb A_E)^\times$ be a homomorphism whose values all have trivial infinite part and trivial component at every finite place other than $v$, and whose $v$-component is the identity, and let $\theta\colon (E_v)^\times \to D(w)$ be a homomorphism into the decomposition subgroup of the valuation subring of $w$ over $E$ with $\theta(z)=r(\iota_v z)$ as elements of $\mathrm{Gal}(F/E)$. The conclusion is that $\theta$ is a local reciprocity map for the embedding $E_v \to F_w$ induced by base change of adic completions, with group $D(w)$: $\theta$ is surjective; for $a \in (E_v)^\times$, $\theta(a)=1$ iff $a$ is the product $\prod^{\mathrm f}_{h \in D(w)} h\cdot b$ for some $b \in F_w$; for every subgroup $H' \le D(w)$, every $a$ and every $b \in F_w$ fixed by $H'$ with $\prod^{\mathrm f}_{c \in D(w)/H'} (\text{a representative of } c)\cdot b = a$, one has $\theta(a) \in H'$; the image under $\theta$ of the units $\{a : \mathrm{v}(a)=1\}$ is the inertia set of $F_w$ under $D(w)$; and for every arithmetic Frobenius $\varphi$ in $D(w)$, every $a$ and every $n \in \mathbb Z$ with $\mathrm{v}(a)=\exp(-n)$, the element $\theta(a)\varphi^{-n}$ lies in that inertia set.
--
--   This is the compatibility of the global idelic Artin map with local reciprocity: the composite of the global map with the single-place embedding at a finite place $v$ satisfies all the defining properties of a local reciprocity map for the extension $F_w/E_v$ with group the decomposition subgroup at $w$. It assembles the separate statements about the single-place idelic Artin map (image of the ideles trivial outside $v$, triviality criterion, membership in a subgroup, and congruence with a power of Frobenius modulo inertia), and is used in the comparison of the idelic Artin map with the upper ramification filtration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_isLocalReciprocityMap_of_idelicArtinMap_single.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LocalReciprocity_IsLocalReciprocityMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open NumberField
open M4aHerbrand
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.isLocalReciprocityMap_of_idelicArtinMap_single
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)

    (ιv : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ)
    (hιv : ∀ z, ιv z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hιv' : ∀ z, finPart v (ιv z) = z)
    (θ : (v.adicCompletion E)ˣ →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hθ : ∀ z, ((θ z : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = r (ιv z)) :
    LocalReciprocity.IsLocalReciprocityMap (v.adicCompletion E) (w.adicCompletion F)
      (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
        v.adicCompletion E →+* w.adicCompletion F)
      ↥(NumberField.PlaceDecomp.decomp E F w) θ := by sorry
