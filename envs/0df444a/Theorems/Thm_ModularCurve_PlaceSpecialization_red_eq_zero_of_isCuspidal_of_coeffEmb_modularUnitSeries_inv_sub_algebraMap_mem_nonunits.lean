-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_red_eq_zero_of_isCuspidal_of_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits
-- name    : ModularCurve.PlaceSpecialization.red_eq_zero_of_isCuspidal_of_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/1b36302f-e422-5ee3-91d6-a0dcbc41c509
-- title:
--   At cuspidal places, finite A-values of u⁻¹ reduce to zero
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Fix moreover data $\Phi$ of type `ModularPolynomialData q` (a monic polynomial in two variables over $\mathbb Z$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions), a proof `hKr` that its reduction modulo $q$ equals $(C(X)^q-X)(C(X)-X^q)$, and proofs $h\alpha$, $h\beta$ that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the base-changed level-one modular function field into `modularFunctionFieldBar (1 * q)` are integral ring homomorphisms; let $P$ be a place specialisation of this data, i.e. a map on places together with a homomorphism on degree-zero divisor classes satisfying the order-compatibility axioms of `PlaceSpecialization`. Let $W$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ (a proper valuation subring containing the base field and a principal ideal ring) which is cuspidal for $P$, meaning $\operatorname{ord}_W(j-a)\le 0$ for every $a\in A$. Write $u$ for the element of `modularFunctionFieldBar (1 * q)` with $q$-expansion `modularUnitSeries (1 * q)` $=\Delta\cdot\Delta_{q}^{-1}$. Then for every $a\in A$ such that $u^{-1}-a$ is a non-unit of the valuation subring of $W$, one has $\mathrm{red}(a)=0$.
--
--   The statement says that on the cuspidal region of the chosen place specialisation of $X_0(q)$ the modular unit $\Delta/\Delta_q$ has no $A$-integral value whose reduction is nonzero for its inverse, so such a place can only chart-reduce to the cusp where $1/\bar u$ vanishes. It is the extra input used by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided), which runs the one-sided first branch divisor law for an arbitrary principal divisor rather than only for divisors whose support avoids the cuspidal region.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_red_eq_zero_of_isCuspidal_of_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.red_eq_zero_of_isCuspidal_of_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W)
    (a : A)
    (ha : ((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
        ↥(modularFunctionFieldBar (1 * q)))⁻¹
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
          ∈ W.toValuationSubring.nonunits) :
    red a = 0 := by sorry
