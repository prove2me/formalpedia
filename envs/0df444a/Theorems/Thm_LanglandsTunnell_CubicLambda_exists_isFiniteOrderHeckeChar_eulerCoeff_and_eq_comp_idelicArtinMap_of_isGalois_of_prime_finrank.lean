-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank
-- name    : LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/ba170632-7a96-5d55-8f8f-bd9e442b1547
-- title:
--   Hecke character of a prime-degree abelian extension, via the Artin map
-- statement:
--   Let $E$ and $F$ be number fields with $F/E$ Galois and $\mathrm{Gal}(F/E)$ commutative, and suppose $\ell = [F:E]$ is prime. The assertion is that there is a monoid homomorphism $\psi : (\mathbb{A}_E)^\times \to \mathbb{C}^\times$ which is a finite-order Hecke character in the sense of the project, i.e. $\psi$ is trivial on the image of $E^\times$, continuous, and of finite order, and which satisfies $\psi^{\ell} = 1$; such that for every prime $\mathfrak q$ of $\mathcal O_E$ and every prime $\mathfrak Q$ of $\mathcal O_F$ contracting to $\mathfrak q$, the Euler coefficient $\mathrm{eulerCoeff}\,E\,\psi\,\mathfrak q$ — defined as $\psi$ of the uniformizer idele at $\mathfrak q$ when $\psi$ is unramified at $\mathfrak q$ and as $0$ otherwise — is a primitive root of unity of order the inertia degree $f(\mathfrak Q/\mathfrak q)$ whenever $e(\mathfrak Q/\mathfrak q)=1$, and vanishes whenever $e(\mathfrak Q/\mathfrak q)\neq 1$; and, in addition, the construction of $\psi$ is exported: there exist an ideal $\mathfrak f \subseteq \mathcal O_E$ which is an admissible modulus of degree $\ell$ for $F/E$ (nonzero, and divisible by $v^{\,\mathrm{admissibleExpOfDegree}\,E\,\ell\,v}$ for every finite place $v$ whose chosen prime above in $F$ has nontrivial inertia subgroup), a homomorphism $r : (\mathbb{A}_E)^\times \to \mathrm{Gal}(F/E)$ and a homomorphism $\chi : \mathrm{Gal}(F/E) \to \mathbb{C}^\times$ with: the principal ideles contained in $\ker r$; $\ker r$ equal to the join of the principal ideles with the image of the idelic norm attached to the base change $\mathbb{A}_E \to \mathbb{A}_F$; $r$ surjective; $r(u) = \prod_{v}^{\mathrm{f}} (\mathrm{artinFrob}\,E\,F\,v)^{\mathrm{ord}_v(u_{\mathrm{fin}})}$ (a finprod over the finite places, the exponent being minus the logarithm of the $v$-adic valuation of the finite component of $u$) for every idele $u$ satisfying $\mathrm{IsAdjuster}\,E\,\mathfrak f\,u\,1$, that is, $u$ has valuation $1$ and $u-1$ has valuation at most $\exp(-\mathrm{ord}_v \mathfrak f)$ at each $v \mid \mathfrak f$ and positive archimedean real projection at each real embedding; $\chi$ injective; and $\psi = \chi \circ r$.
--
--   This is the class-field-theoretic input to the Langlands–Tunnell argument: the order-$\ell$ Hecke character of $E$ cutting out the prime-degree abelian extension $F$, with Euler factors recording the splitting behaviour of primes, packaged together with the idelic Artin map $r$ and the injective Galois character $\chi$ through which it factors. Exporting $r$ and $\chi$ rather than $\psi$ alone allows local class field theory (the behaviour of $r$ on higher unit groups) to be applied to this same $\psi$; it is used in the companion statement bounding the character's local behaviour in terms of the factorisation of the discriminant over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank.lean

import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField.AdelicLevel NumberField.TateGlobal HeckeCharacter M4aHerbrand M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin LanglandsTunnell.Converse AutomorphicForm
open NumberField

open scoped IsMulCommutative

theorem LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank
    (E : Type) [Field E] [NumberField E] (F : Type) [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)] (hℓ : (Module.finrank E F).Prime) :
    ∃ ψ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsFiniteOrderHeckeChar E ψ ∧ ψ ^ Module.finrank E F = 1 ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 E)) (𝔔 : HeightOneSpectrum (𝓞 F)), 𝔔.under (𝓞 E) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff E ψ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff E ψ 𝔮 = 0)) ∧
      ∃ (𝔣 : Ideal (𝓞 E)) (_ : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
        (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F)) (χ : (F ≃ₐ[E] F) →* ℂˣ),
        principalIdeles (𝓞 E) E ≤ r.ker ∧
        r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range ∧
        Function.Surjective r ∧
        (∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
          r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v) ∧
        Function.Injective χ ∧ ψ = χ.comp r := by sorry
