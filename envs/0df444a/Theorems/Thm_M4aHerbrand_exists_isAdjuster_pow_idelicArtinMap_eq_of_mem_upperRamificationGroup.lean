-- Prove2me | Theorems.Thm_M4aHerbrand_exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup
-- name    : M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a2349450-278b-55d0-b05c-13942e3dbb1f
-- title:
--   Upper ramification groups lie in the local image of the idelic Artin map
-- statement:
--   Let $F/E$ be a finite Galois extension of number fields whose Galois group $F \simeq_{\mathrm{alg}[E]} F$ is commutative, and let $\mathfrak f$ be an ideal of $\mathcal O_E$ which is an admissible modulus for the degree $[F:E]$, i.e. $\mathfrak f \neq \bot$ and for every finite place $u$ of $E$ such that the chosen prime of $\mathcal O_F$ above $u$ has nontrivial inertia subgroup in $\mathrm{Gal}(F/E)$, the power $u^{\,\mathrm{admissibleExpOfDegree}\,E\,[F:E]\,u}$ divides $\mathfrak f$. Let $r$ be a monoid homomorphism from the ideles $(\mathbb A_E)^\times$ to $\mathrm{Gal}(F/E)$ such that: the principal ideles (the image of $E^\times$) lie in $\ker r$; $\ker r$ is the join of the principal ideles with the range of the idelic norm attached to `genuineBaseChange E F`; $r$ is surjective; and for every idele $u$ satisfying `IsAdjuster E 𝔣 u 1` one has $r(u) = \prod_{v}^{f} (\mathrm{artinFrob}\,E\,F\,v)^{\mathrm{placeOrd}\,E\,(\mathrm{projFin}\,E\,u)\,v}$, the finprod over finite places of powers of the Frobenius at the chosen prime above $v$, the exponent being $-\log$ of the $v$-adic valuation of the finite part of $u$. Let $v$ be a finite place of $E$, let $w$ be a finite place of $F$ with $w$ lying over $v$ ($w.\mathrm{under}\,\mathcal O_E = v$), let $n \geq 1$, and let $\sigma \in \mathrm{Gal}(F/E)$ lie in the image, under the inclusion of the decomposition subgroup of the valuation subring of $w$ over $E$, of the $n$-th upper-numbering ramification group of that valuation subring. Then there is an idele $x$ such that: $x$ lies in `idelesTrivialOn (𝓞 E) E {v}ᶜ`, i.e. its infinite part is $1$ and its finite component at every place other than $v$ is $1$; `IsAdjuster E (v.asIdeal ^ n) x 1` holds, i.e. at each finite place dividing $v^n$ the finite part of $x$ has valuation $1$ and $x - 1$ has valuation at most $\exp(-e)$ with $e$ the multiplicity of that place in $v^n$, and the archimedean real projection of $x$ is positive at every real embedding of $E$; and $r(x) = \sigma$.
--
--   This is the surjectivity half of the compatibility between the idelic Artin map and the ramification filtration in the upper numbering: the $n$-th upper ramification group at $w \mid v$ is contained in the image under $r$ of the local unit group $1 + \mathfrak p_v^{\,n}$, embedded in the ideles at the place $v$. Together with the converse inclusion it governs the minimality of the local conductor exponent, and it is used in showing that an abelian Artin symbol is nontrivial on the unit filtration below the conductor exponent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open M4aHerbrand
open scoped IsMulCommutative NumberField.PlaceDecomp

theorem M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup
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
    (n : ℕ) (hn : 1 ≤ n)
    (σ : F ≃ₐ[E] F) (hσ : σ ∈ (ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) (n : ℚ)).map
          (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype) :
    ∃ x : (AdeleRing (𝓞 E) E)ˣ, x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) ∧
      IsAdjuster E (v.asIdeal ^ n) x 1 ∧ r x = σ := by sorry
