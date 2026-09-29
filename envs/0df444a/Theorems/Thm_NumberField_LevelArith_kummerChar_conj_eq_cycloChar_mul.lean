-- Prove2me | Theorems.Thm_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul
-- name    : NumberField.LevelArith.kummerChar_conj_eq_cycloChar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/2fb1b2dc-75bb-51a3-9582-74cdccdf4028
-- title:
--   Conjugation rule for the Kummer character: cyclotomic twist
-- statement:
--   Let $p$ be a prime, let $\zeta$ be a primitive $p$-th root of unity in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $F$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ with $\zeta \in F$. Let $\gamma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ which maps $F$ into itself, let $\sigma$ lie in the fixing subgroup of $F$ (the automorphisms fixing $F$ pointwise), and assume that $\gamma\sigma\gamma^{-1}$ also lies in that fixing subgroup. Let $x, x'$ be units of $F$ with $x' = \gamma(x)$ as elements of $\overline{\mathbb{Q}}$. Here `kummerChar p ζ hζ F x σ` is the element $a \in \mathbb{Z}/p$ characterised by $\sigma(y) = \zeta^{a.\mathrm{val}}\,y$, where $y$ is the chosen $p$-th root `kummerRoot p F x` of $x$ in $\overline{\mathbb{Q}}$, and `cycloChar p γ` is the value at $\gamma$ of the mod $p$ cyclotomic character, obtained from Mathlib's `modularCyclotomicCharacter` of $\overline{\mathbb{Q}}$, a unit of $\mathbb{Z}/p$. The conclusion is the identity in $\mathbb{Z}/p$
--   $$\mathrm{kummerChar}(x')(\gamma\sigma\gamma^{-1}) = \mathrm{cycloChar}(\gamma)\cdot \mathrm{kummerChar}(x)(\sigma).$$
--
--   This is the equivariance of the Kummer character under an outer conjugation, with the cyclotomic twist: transporting by $\gamma$ the class of $x$ and the group element $\sigma$ multiplies the character by the mod $p$ cyclotomic character of $\gamma$. It is the input that makes the Kummer characters attached to $F^{\times}/(F^{\times})^{p}$ into a module over the larger Galois group twisted by $\mu_p$, and is used in the construction of the Selmer representation isomorphism [`NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom`](thm.html#NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul.lean

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

theorem NumberField.LevelArith.kummerChar_conj_eq_cycloChar_mul
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hγF : ∀ z ∈ F, γ z ∈ F)
    (σ : ↥F.fixingSubgroup) (hconj : γ * (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * γ⁻¹ ∈ F.fixingSubgroup)
    (x x' : (↥F)ˣ) (hx' : ((x' : ↥F) : AlgebraicClosure ℚ) = γ ((x : ↥F) : AlgebraicClosure ℚ)) :
    kummerChar p ζ hζ F x' ⟨γ * (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * γ⁻¹, hconj⟩ = ((cycloChar p γ : ZMod p)) * kummerChar p ζ hζ F x σ := by sorry
