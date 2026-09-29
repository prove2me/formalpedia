-- Prove2me | Theorems.Thm_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation
-- name    : NumberField.LevelArith.kummerChar_isLevelConstant_iff_forall_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8484a2f8-607c-5dc8-9317-892dd17a5fd9
-- title:
--   Level-constancy of the Kummer character via divisibility of valuations
-- statement:
--   Fix a prime $p$ and a finite set $S$ of primes containing $p$ (the element `pPrime p` of `Nat.Primes`), let $\zeta$ be an element of $\overline{\mathbb{Q}}$ that is a primitive $p$-th root of unity, and let $F$ be a subfield of $\overline{\mathbb{Q}}$ containing $\mathbb{Q}$, of finite degree over $\mathbb{Q}$, with $\zeta \in F$ and satisfying `F.IsUnramifiedOutside S`: $F$ is finite over $\mathbb{Q}$ and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ is contained in the subgroup fixing $F$ pointwise. For a unit $x$ of $F$, the following are equivalent. First: there is a subfield $F'$ of $\overline{\mathbb{Q}}$ containing $\mathbb{Q}$, again unramified outside $S$ in the above sense, such that every $\sigma$ in the fixing subgroup of $F$ whose underlying automorphism also fixes $F'$ pointwise satisfies $\mathrm{kummerChar}\,p\,\zeta\,h_\zeta\,F\,x\,\sigma = 0$ in $\mathbb{Z}/p$, this value being the reduction of the natural number chosen as a witness for `exists_kummerExp`. Second: for every height-one prime $w$ of $\mathcal{O}_F$ which does not lie over $S$, i.e. such that no prime $q \in S$ has $q \in w$, the integer $\mathrm{toAdd}(w.\mathrm{valuationOfNeZero}\,x)$, the $w$-adic valuation of $x$, is divisible by $p$.
--
--   This is the tame-ramification criterion for Kummer extensions in the form needed for level bookkeeping: the Kummer character of $x$ is killed by the Galois group of some field unramified outside $S$ exactly when $x$ satisfies the Selmer condition $p \mid v_w(x)$ at all finite places away from $S$. It is used in the construction of the isomorphism between the mod $p$ Selmer representation and the module of level-constant homomorphisms, [`NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom`](thm.html#NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.kummerChar_isLevelConstant_iff_forall_dvd_valuation
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) (hζF : ζ ∈ F) (x : (↥F)ˣ) :
    (∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F'.IsUnramifiedOutside S ∧
        ∀ σ : ↥F.fixingSubgroup, (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F'.fixingSubgroup → kummerChar p ζ hζ F x σ = 0) ↔
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F), w ∉ placesOverPrimes ↥F (S : Set Nat.Primes) →
        (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x) := by sorry
