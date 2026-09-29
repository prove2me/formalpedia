-- Prove2me | Theorems.Thm_NumberField_LevelArith_inertia_apply_eq_of_dvd_valuation
-- name    : NumberField.LevelArith.inertia_apply_eq_of_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/99d32743-82ba-5a6b-b459-d1c52d632fc0
-- title:
--   Inertia above w ∤ p fixes p-th roots
-- statement:
--   Let $p$ be a prime, let $F$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ that is finite over $\mathbb{Q}$, let $x \in F^{\times}$, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$. Assume there is a prime $q \neq p$ with $q \in w$, so that $w$ has residue characteristic different from $p$, and assume that $p$ divides the integer $v_w(x)$, the additive value of the normalised $w$-adic valuation of the nonzero element $x$. Let $y \in \overline{\mathbb{Q}}$ satisfy $y^{p} = x$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ extending $w$, in the sense that an element of $F$ lies in $A$ precisely when its $w$-adic valuation is at most $1$. Finally let $\sigma$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in `inertiaSubgroupIn`, i.e. in the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$, and suppose $\sigma$ fixes every element of $F$. Then $\sigma y = y$.
--
--   This is the local tameness statement of Kummer theory: for a place $w$ of residue characteristic different from $p$, the extension $F(x^{1/p})$ is unramified at $w$ as soon as $p \mid v_w(x)$, here in the pointwise form that inertia at $w$ fixes each $p$-th root of $x$. It feeds the construction of Selmer-type modules and the production of cocycles unramified outside a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_inertia_apply_eq_of_dvd_valuation.lean

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

theorem NumberField.LevelArith.inertia_apply_eq_of_dvd_valuation
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]
    (x : (↥F)ˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F))
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqw : ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal)
    (hw : (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x))
    (y : AlgebraicClosure ℚ) (hy : y ^ p = ((x : ↥F) : AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ∀ z : ↥F, (z : AlgebraicClosure ℚ) ∈ A ↔ w.valuation ↥F z ≤ 1)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hσF : ∀ z : ↥F, σ z = z) :
    σ y = y := by sorry
