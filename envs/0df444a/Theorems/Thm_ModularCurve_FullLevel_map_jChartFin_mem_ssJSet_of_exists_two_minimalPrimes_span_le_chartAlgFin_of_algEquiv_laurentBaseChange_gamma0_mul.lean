-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_of_algEquiv_laurentBaseChange_gamma0_mul
-- name    : ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_of_algEquiv_laurentBaseChange_gamma0_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/4b056b72-362a-58b1-9576-dc071b2fea29
-- title:
--   Crossing points of the special fibre are supersingular (transported)
-- statement:
--   Let $q$ be a prime, $M'\ge 1$ with $q\nmid M'$, and $L$ a field of characteristic $0$. Let $K_0$ be an intermediate field of $L((q))/L$ together with an $L$-algebra isomorphism $e$ from $K_0$ onto [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M' * q)))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. onto the subfield of $L((q))$ generated over $L$ by the coefficientwise image along $\mathbb Q\to L$ of the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients $\mathrm{(q\text{-}expansion\ of\ }f)/(\mathrm{q\text{-}expansion\ of\ }g)$ of modular forms $f,g$ of equal weight for $\Gamma_0(M'q)$ with integral $q$-expansions and $g\neq 0$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in the maximal ideal, with $\varpi$ generating that maximal ideal, and let $K_0$ be an $A$-algebra compatibly. Let $j\in K_0$ be nonzero with $e(j)$, read as a Laurent series over $L$, equal to the coefficientwise image of the $q$-expansion $q^{-1}\cdot\mathrm{jNumQ}$ of the modular invariant. Write $B$ for `chartAlgFin A K₀ j`, the subalgebra of elements of $K_0$ integral over $A[j]$. Let $y$ be a prime of $B$ containing $\varpi$ and containing two distinct minimal primes of $\varpi B$, let $\Omega$ be an algebraically closed field of characteristic $q$, and let $\varphi:B\to\Omega$ be a ring homomorphism with kernel $y$. Then $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7): every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero $q$-torsion point.
--
--   This is the statement that the crossing points of the special fibre of the two-chart integral model of $X_0(M'q)$ over a discrete valuation ring are supersingular, in a form where the function field is only prescribed up to an $L$-algebra isomorphism onto the $q$-expansion field of $\Gamma_0(M'q)$, so that it can be applied to an isomorphic copy sitting inside a larger level field. It is obtained by transport of structure from the corresponding statement with $K_0$ equal to that field on the nose, and is used in the supersingularity statement for crossing points phrased via the Gauss points of the $X_H$ model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_of_algEquiv_laurentBaseChange_gamma0_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_of_algEquiv_laurentBaseChange_gamma0_mul
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]

    (K₀ : IntermediateField L (LaurentSeries L))
    (e : ↥K₀ ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M' * q)))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j : ↥K₀)
    (hj : ((e j : ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M' * q))))) : LaurentSeries L) =
        ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j)) [y.IsPrime]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j) ϖ ∈ y)
    (htwo : ∃ 𝔭 ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j) ϖ}).minimalPrimes,
        ∃ 𝔭' ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j) ϖ}).minimalPrimes,
          𝔭 ≠ 𝔭' ∧ 𝔭 ≤ y ∧ 𝔭' ≤ y)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j) →+* Ω) (hφ : RingHom.ker φ = y) :
    φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j) ∈ ModularCurve.ssJSet q Ω := by sorry
