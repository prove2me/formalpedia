-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
-- name    : NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/ffbd2c4f-e9cc-5a77-8eab-cc43288e0656
-- title:
--   Inertia above w moves a p-th root when p ∤ v_w(x)
-- statement:
--   Let $p$ be a prime, and let $F$ be an intermediate field of $\mathbb{Q}$ inside $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is finite-dimensional over $\mathbb{Q}$. Let $x$ be a unit of $F$, let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$, and assume that the integer attached to the $w$-adic valuation of $x$ — the value `w.valuationOfNeZero x` in the multiplicative group of integers, transported to $\mathbb{Z}$ by `Multiplicative.toAdd` — is not divisible by $p$. Let $y \in \overline{\mathbb{Q}}$ satisfy $y^p = x$, the image of $x$ under the inclusion $F \subseteq \overline{\mathbb{Q}}$. The conclusion asserts the existence of a valuation subring $A$ of $\overline{\mathbb{Q}}$ with the property that for every $z \in F$ one has $z \in A$ if and only if $w.\mathrm{valuation}(z) \le 1$ (so $A$ induces exactly $w$ on $F$), together with an element $\sigma$ of `A.inertiaSubgroupIn ℚ` — that is, of the image in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$, of the inertia subgroup of $A$ over $\mathbb{Q}$ — such that $\sigma z = z$ for all $z \in F$ while $\sigma y \neq y$.
--
--   This is the ramification half of the local theory of Kummer extensions: if the $w$-adic valuation of $x$ is not divisible by $p$, then $F(x^{1/p})$ is ramified at $w$, expressed here by exhibiting an inertia element above $w$ that fixes $F$ and moves the chosen $p$-th root $y$. It is used in the comparison of the Kummer character of a class with the condition that $p$ divide all valuations, through [`NumberField.LevelArith.kummerChar_isLevelConstant_iff_forall_dvd_valuation`](thm.html#NumberField.LevelArith.kummerChar_isLevelConstant_iff_forall_dvd_valuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation.lean

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

theorem NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]
    (x : (↥F)ˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F))
    (hw : ¬ (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x))
    (y : AlgebraicClosure ℚ) (hy : y ^ p = ((x : ↥F) : AlgebraicClosure ℚ)) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), (∀ z : ↥F, (z : AlgebraicClosure ℚ) ∈ A ↔ w.valuation ↥F z ≤ 1) ∧
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, (∀ z : ↥F, σ z = z) ∧ σ y ≠ y := by sorry
