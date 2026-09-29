-- Prove2me | Theorems.Thm_M4aHerbrand_prod_idelicArtinMap_single_eq_one
-- name    : M4aHerbrand.prod_idelicArtinMap_single_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/8e89768d-ac28-5963-81d4-5fbceecdc37e
-- title:
--   Triviality of the Artin map product on single-place idèles
-- statement:
--   Let $F/E$ be a Galois extension of number fields whose Galois group $F \simeq_{\mathrm{alg}[E]} F$ is commutative, let $\mathfrak f$ be an ideal of $\mathcal O_E$ that is an admissible modulus for the degree $[F:E]$, that is, $\mathfrak f \neq 0$ and $v^{e}\mid\mathfrak f$ (with $e$ the prescribed admissible exponent for that degree) for every finite place $v$ whose chosen prime above in $F$ has nontrivial inertia, and let $r$ be a group homomorphism from the idèle units $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ satisfying: the principal idèles, i.e. the image of $E^\times$, lie in $\ker r$; $\ker r$ is the join of the principal idèles with the image of the idelic norm attached to the base change `genuineBaseChange E F`; $r$ is surjective; and for every idèle $u$ which is an adjuster for $\mathfrak f$ relative to $1$ (all components at places dividing $\mathfrak f$ have valuation $1$ and are congruent to $1$ to the precision given by the exponent of $v$ in $\mathfrak f$, and the real projection of $u$ at each real embedding is positive), $r(u)$ equals the finite product over finite places $v$ of the arithmetic Frobenius `artinFrob E F v` raised to the power $-\log\lvert u_v\rvert$. Assume further that every infinite place $v$ of $F$ has trivial stabiliser in $\mathrm{Gal}(F/E)$. Given $a \in E^\times$ and a family $x$ of idèles indexed by the finite places of $E$ such that $x_v$ has trivial archimedean part and trivial component at every $w \neq v$, and component at $v$ the image of $a$ in $(E_v)^\times$, and given a finite set $S$ of finite places containing every $v$ with $v \mid \mathfrak f$ and every $v$ at which the valuation of $a$ is not $1$, the conclusion is $\prod_{v\in S} r(x_v)=1$.
--
--   This is Artin's reciprocity law in its single-place form, stated over an axiomatised idelic Artin map: the Frobenius contributions of a global element, spread out over the finite places, cancel. It is the shape in which reciprocity enters the cyclic-layer computation, and it is used here in the proof that the relevant finite sum of local terms divided by the orders of the decomposition groups vanishes for cyclic extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_prod_idelicArtinMap_single_eq_one.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.prod_idelicArtinMap_single_eq_one
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (a : Eˣ) (x : HeightOneSpectrum (𝓞 E) → (AdeleRing (𝓞 E) E)ˣ)
    (hx : ∀ v : HeightOneSpectrum (𝓞 E), x v ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxv : ∀ v : HeightOneSpectrum (𝓞 E), finPart v (x v) = Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) a)
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS𝔣 : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣 → v ∈ S)
    (hSa : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S → (v.valuation E) (a : E) = 1) :
    ∏ v ∈ S, r (x v) = 1 := by sorry
