-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_kummerChar_eq_of_continuous
-- name    : NumberField.LevelArith.exists_kummerChar_eq_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/7242b891-f10b-5099-aa9b-9880f7687b61
-- title:
--   Every continuous ℤ/p-character is a Kummer character
-- statement:
--   Fix a prime $p$ and an element $\zeta$ of $\overline{\mathbb{Q}}$ (Mathlib's `AlgebraicClosure ℚ`) which is a primitive $p$-th root of unity, as witnessed by `hζ`. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$ and contains $\zeta$, and write $F.\mathrm{fixingSubgroup}$ for the subgroup of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ fixing $F$ pointwise. Let $\chi : F.\mathrm{fixingSubgroup} \to \mathbb{Z}/p$ be a function satisfying $\chi(\sigma\tau) = \chi(\sigma) + \chi(\tau)$ for all $\sigma,\tau$, and suppose there is a further intermediate field $F_0$, finite-dimensional over $\mathbb{Q}$ with $F \le F_0$, such that $\chi(\sigma) = 0$ whenever the automorphism underlying $\sigma$ fixes $F_0$ pointwise; this finite-level condition plays the role of continuity. The conclusion asserts the existence of a unit $x$ of $F$ such that for every $\sigma \in F.\mathrm{fixingSubgroup}$ one has $\mathrm{kummerChar}\,p\,\zeta\,h\zeta\,F\,x\,\sigma = \chi(\sigma)$, where `kummerChar` assigns to $x$ and $\sigma$ the class in $\mathbb{Z}/p$ of the natural-number exponent chosen as a witness for `exists_kummerExp p ζ hζ F x σ`.
--
--   This is the surjectivity half of Kummer theory over a number field containing $\mu_p$: the Kummer characters attached to units of $F$ exhaust the homomorphisms $\mathrm{Gal}(\overline{\mathbb{Q}}/F) \to \mathbb{Z}/p$ that are trivial on some open subgroup. It is used in the construction of the isomorphism between the Selmer representation and level-constant homomorphisms, via [`NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom`](thm.html#NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom); the proof cites the surjectivity of the Kummer map [`groupCohomology.Kummer.kummerHom_surjective`](thm.html#groupCohomology.Kummer.kummerHom_surjective) for finite Galois extensions together with normality of the intermediate level field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_kummerChar_eq_of_continuous.lean

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

theorem NumberField.LevelArith.exists_kummerChar_eq_of_continuous
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hζF : ζ ∈ F)
    (χ : ↥F.fixingSubgroup → ZMod p) (hχ : ∀ σ τ : ↥F.fixingSubgroup, χ (σ * τ) = χ σ + χ τ)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F₀] (hF₀ : F ≤ F₀)
    (hχ₀ : ∀ σ : ↥F.fixingSubgroup, (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F₀.fixingSubgroup → χ σ = 0) :
    ∃ x : (↥F)ˣ, ∀ σ : ↥F.fixingSubgroup, kummerChar p ζ hζ F x σ = χ σ := by sorry
