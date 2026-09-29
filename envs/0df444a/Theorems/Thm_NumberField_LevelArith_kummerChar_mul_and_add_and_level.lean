-- Prove2me | Theorems.Thm_NumberField_LevelArith_kummerChar_mul_and_add_and_level
-- name    : NumberField.LevelArith.kummerChar_mul_and_add_and_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8589ef57-7025-516e-856b-b5a6a033b4fd
-- title:
--   Kummer character: bi-additive and trivial on Gal(ℚ̄/F(y))
-- statement:
--   Let $p$ be a prime, let $\zeta$ be an element of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a primitive $p$-th root of unity, and let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $\zeta \in F$. For a unit $x$ of $F$, `kummerRoot p F x` is a fixed choice $y$ of element of $\overline{\mathbb{Q}}$ with $y^p = x$ (obtained from algebraic closedness), and for $\sigma$ in the fixing subgroup $F.\mathrm{fixingSubgroup} \le \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of $F$, `kummerChar p ζ hζ F x σ` is the element of $\mathbb{Z}/p$ obtained by reducing a chosen natural number $n$ with $\sigma(y) = \zeta^{n} y$. Three assertions are made. First, for every unit $x$ of $F$ and all $\sigma, \tau$ in the fixing subgroup of $F$, the character is additive in the group variable: its value at $\sigma\tau$ is the sum of its values at $\sigma$ and at $\tau$. Second, for all units $x, x'$ of $F$ and every such $\sigma$, its value at $x x'$ is the sum of its values at $x$ and at $x'$. Third, for every unit $x$ and every such $\sigma$, if $\sigma$ lies in the fixing subgroup of the compositum $F \sqcup \mathbb{Q}(y)$, where $y =$ `kummerRoot p F x`, then the value of the character at $(x,\sigma)$ is $0$.
--
--   This is the basic formal property of the Kummer character attached to a class in $F^\times/(F^\times)^p$ when $\mu_p \subseteq F$: the a priori crossed homomorphism $\sigma \mapsto \sigma(y)/y$ becomes a genuine homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}/F) \to \mathbb{Z}/p$, additive in $x$ and trivial on the open subgroup fixing $F(y)$ (whence continuity). It feeds the identification of the Selmer representation with level-constant homomorphisms and the valuation-theoretic criterion for the Kummer character to be level constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_kummerChar_mul_and_add_and_level.lean

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

theorem NumberField.LevelArith.kummerChar_mul_and_add_and_level
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F) :
    (∀ (x : (↥F)ˣ) (σ τ : ↥F.fixingSubgroup), kummerChar p ζ hζ F x (σ * τ) = kummerChar p ζ hζ F x σ + kummerChar p ζ hζ F x τ) ∧
    (∀ (x x' : (↥F)ˣ) (σ : ↥F.fixingSubgroup), kummerChar p ζ hζ F (x * x') σ = kummerChar p ζ hζ F x σ + kummerChar p ζ hζ F x' σ) ∧
    (∀ (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup),
      (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ (F ⊔ IntermediateField.adjoin ℚ {kummerRoot p F x}).fixingSubgroup → kummerChar p ζ hζ F x σ = 0) := by sorry
