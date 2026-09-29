-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum
-- name    : NumberField.LevelArith.exists_placesAbove_inr_embedding_heightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/524eb19a-8e86-56e1-9e3c-2bd4d528ec20
-- title:
--   Places of the level above q as primes of 𝒪_{L'}
-- statement:
--   Let $K \le L$ be intermediate fields of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` over $\mathbb{Q}$, each of finite degree over $\mathbb{Q}$, and write $L' =$ `levelField K L hKL` for $L$ viewed as an extension of $K$ (`IntermediateField.extendScalars`), assumed normal over $K$. Assume `IsNormalLevel K L`: for every $g$ in the fixing subgroup $\Gamma_K$ of $K$ and every $s$ in the fixing subgroup $\Gamma_L$ of $L$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ one has $g s g^{-1} \in \Gamma_L$. Let $S$ be a finite set of rational primes and $q \in S$. Put $X = \Gamma_L \backslash \bigl(\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) / \mathrm{im}\,(\mathrm{extArithLoc}\,S\,(\mathrm{Sum.inr}\,q))\bigr)$, the set of orbits of $\Gamma_L$ on the coset space of the image of the chosen local-to-global homomorphism `primeLocalToGlobal` at $q$. The assertion is that there is a map $e$ from $X$ to the height-one spectrum of $\mathcal{O}_{L'}$ which is injective, whose range is exactly the set of primes $w$ with $q \in w$ (i.e. the image of $q \in \mathbb{N}$ in $\mathcal{O}_{L'}$ lies in `w.asIdeal`), and which is equivariant: for $\gamma \in \Gamma_K$ and $x \in X$, $e$ of the class of $\gamma \cdot x$ (the action of `orbitQuotientAction`) equals `levelGal K L hKL` $\gamma$, the restriction of $\gamma$ to a $K$-algebra automorphism of $L'$, applied to $e(x)$ under the pointwise action on primes.
--
--   This identifies the $q$-component of the Galois-set index of finite places of a level, described adelically as $\Gamma_L$-orbits on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ modulo the local decomposition image at $q$, with the set of primes of $\mathcal{O}_{L'}$ above $q$, compatibly with the actions of $\Gamma_K$ and of $\mathrm{Gal}(L'/K)$. It is used to produce the equivalence `exists_placesAbove_inr_equiv_primesOver` and, through it, the equivariant $S$-unit rank computation `finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

theorem NumberField.LevelArith.exists_placesAbove_inr_embedding_heightOneSpectrum
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (q : ↥S) :
    ∃ e : placesAbove L S (Sum.inr q) → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField K L hKL)),
      Function.Injective e ∧
      Set.range e = {w | ((((q : Nat.Primes) : ℕ) : NumberField.RingOfIntegers ↥(levelField K L hKL))) ∈ w.asIdeal} ∧
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)),
        e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ x) =
          levelGal K L hKL γ • e x := by sorry
