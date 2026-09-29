-- Prove2me | Theorems.Thm_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
-- name    : M4aHerbrand.finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/24444626-9def-5e0d-9b02-2ea78b6dffc2
-- title:
--   Product formula for the idelic Artin map, totally positive case
-- statement:
--   Let $F/E$ be a Galois extension of number fields whose Galois group $F \simeq_{\mathrm{alg}[E]} F$ is commutative, and let $\mathfrak f$ be an ideal of $\mathcal O_E$ which is an admissible modulus of degree $[F:E]$: $\mathfrak f \neq 0$, and for every finite place $v$ of $E$ at which the inertia subgroup of the chosen prime `primeAbove E F v` inside $\mathrm{Gal}(F/E)$ is nontrivial, $v^{\,e}$ divides $\mathfrak f$ for the exponent $e =$ `admissibleExpOfDegree E [F:E] v`. Let $r$ be a monoid homomorphism from the idèle group $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ subject to four hypotheses: the principal idèles, i.e. the image of $E^\times$ under $\mathrm{Units.map}$ of $E \to \mathbb A_E$, lie in $\ker r$; $\ker r$ equals the join of the principal idèles with the image of the idelic norm $(\mathbb A_F)^\times \to (\mathbb A_E)^\times$ attached to the base-change datum `genuineBaseChange E F` (that is, $\mathrm{Units.map}$ of the algebra norm of $\mathbb A_F$ over $\mathbb A_E$); $r$ is surjective; and for every idèle $u$ satisfying `IsAdjuster E 𝔣 u 1` — meaning that for each finite place $v$ dividing $\mathfrak f$ the $v$-component of the finite part of $u$ has valuation $1$ and its distance to $1$ is at most $\exp(-\mathrm{ord}_v \mathfrak f)$, and that for each real embedding $\tau$ of $E$ the $\tau$-component of the archimedean part of $u$ is positive — one has $r(u) = \prod^{\mathrm f}_{v} \mathrm{Frob}_v^{\,\mathrm{ord}_v(u)}$, the finitely supported product over finite places of the arithmetic Frobenius `artinFrob E F v` at `primeAbove E F v` raised to $\mathrm{ord}_v$ of the finite part of $u$. Let $\alpha \in E$ be totally positive, i.e. $0 < \tau(\alpha)$ for every ring homomorphism $\tau : E \to \mathbb R$, and let $u \mapsto x_u$ assign to each finite place $u$ of $E$ an idèle whose archimedean part is $1$ and whose $w$-component is $1$ for every finite place $w \neq u$, and whose $u$-component is the image of $\alpha$ in the completion $E_u$. Then the set of finite places $u$ with $r(x_u) \neq 1$ is finite, and $\prod^{\mathrm f}_u r(x_u) = 1$.
--
--   This is the product formula $\prod_v (\alpha, F/E)_v = 1$ of global class field theory for a totally positive element $\alpha$, read off from the four defining properties of the idelic Artin map $r$ rather than from local–global compatibility. It is used in the computation of the conductor of an abelian Artin symbol, feeding the two statements [`ArtinL.Abelian.apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0`](thm.html#ArtinL.Abelian.apply_artinSymbol_eq_one_of_sub_one_mem_pow_mul_of_conductorExponent_le_u0) and [`ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0`](thm.html#ArtinL.Abelian.exists_apply_artinSymbol_ne_one_of_one_le_conductorExponent_u0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive.lean

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

universe u v

theorem M4aHerbrand.finprod_idelicArtinMap_idelesTrivialOn_eq_one_of_totallyPositive
    (E : Type u) (F : Type v) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (α : E) (hpos : ∀ τ : E →+* ℝ, 0 < τ α)
    (x : HeightOneSpectrum (𝓞 E) → (AdeleRing (𝓞 E) E)ˣ)
    (hx : ∀ u : HeightOneSpectrum (𝓞 E), x u ∈ idelesTrivialOn (𝓞 E) E ({u}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxu : ∀ u : HeightOneSpectrum (𝓞 E),
      ((finPart u (x u) : (u.adicCompletion E)ˣ) : u.adicCompletion E) = algebraMap E (u.adicCompletion E) α) :
    (Function.mulSupport fun u : HeightOneSpectrum (𝓞 E) => r (x u)).Finite ∧
      ∏ᶠ u : HeightOneSpectrum (𝓞 E), r (x u) = 1 := by sorry
