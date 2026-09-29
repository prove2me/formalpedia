-- Prove2me | Theorems.Thm_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
-- name    : M4aHerbrand.idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f6f96423-55a8-5cee-b18b-6ebee237787b
-- title:
--   Artin image of level-n units lies in Gⁿ(w∣ v)
-- statement:
--   Let $F/E$ be a Galois extension of number fields whose Galois group $F \simeq_{alg[E]} F$ is commutative, let $\mathfrak f$ be an ideal of $\mathcal O_E$ which is admissible for the degree $[F:E]$, i.e. $\mathfrak f \neq 0$ and, for every finite place $v$ of $E$ at which the inertia subgroup of the chosen prime `primeAbove E F v` inside $\mathrm{Gal}(F/E)$ is nontrivial, $v^{\,\mathrm{admissibleExpOfDegree}\,E\,[F:E]\,v}$ divides $\mathfrak f$. Let $r$ be a homomorphism from the idèle group $(\mathbb A_E)^{\times}$ to $\mathrm{Gal}(F/E)$ such that: the principal idèles lie in $\ker r$; $\ker r$ is the join of the principal idèles with the range of the idelic norm $\mathrm{Units.map}$ of the algebra norm attached to the base change `genuineBaseChange E F`; $r$ is surjective; and for every idèle $u$ satisfying `IsAdjuster E 𝔣 u 1` — at each place $v \mid \mathfrak f$ the finite component $u_v$ has valuation $1$ and $|u_v - 1| \le \exp(-\mathrm{ord}_v(\mathfrak f))$, and $u$ is positive at every real embedding of $E$ — one has $r(u) = \prod_v \mathrm{artinFrob}(v)^{\mathrm{placeOrd}(u)_v}$, the product over finite places of the arithmetic Frobenius at `primeAbove E F v` raised to minus the logarithm of the valuation of the $v$-component of the finite part of $u$. Let $v$ be a finite place of $E$, $w$ a finite place of $F$ lying under which is $v$, $n \ge 1$ a natural number, and $x$ an idèle whose infinite part is $1$ and whose finite components at all places other than $v$ are $1$, and which satisfies `IsAdjuster E (v^n) x 1` (so that the $v$-component has valuation $1$, is congruent to $1$ to level $n$, and the archimedean sign conditions hold). Then $r(x)$ belongs to the image in $\mathrm{Gal}(F/E)$, under the inclusion of the decomposition subgroup of the valuation subring of $w$ over $E$, of the upper-numbering ramification group of that valuation subring at the rational number $n$.
--
--   This is the inclusion half of the ramification-filtration theorem of local class field theory, transported to the global idelic Artin map: level-$n$ units at $v$, embedded as idèles trivial away from $v$, are carried into the $n$-th upper-numbering ramification group at a place $w$ above $v$. It is used to compute conductors and to show that local characters composed with the Artin map are trivial on high-level unit groups, and in the converse statement [`M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup`](thm.html#M4aHerbrand.exists_isAdjuster_pow_idelicArtinMap_eq_of_mem_upperRamificationGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow.lean

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

theorem M4aHerbrand.idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
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
    (x : (AdeleRing (𝓞 E) E)ˣ) (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hxn : IsAdjuster E (v.asIdeal ^ n) x 1) :
    r x ∈ (ValuationSubring.upperRamificationGroup E ((w.valuation F).valuationSubring) (n : ℚ)).map
          (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype := by sorry
