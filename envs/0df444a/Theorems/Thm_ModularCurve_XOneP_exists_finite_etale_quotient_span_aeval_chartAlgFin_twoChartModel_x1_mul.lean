-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/29204792-a35c-53c3-92f9-3e960e01c75e
-- title:
--   Finite étale level quotients of the modular unit on X₁(Mp)
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$, a characteristic-zero field $L$ that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, acting on $K$ compatibly with $L$. Let $j \in K$ be nonzero with Laurent image the coefficientwise image of $q^{-1}\,j_{\mathrm{num}}(q)$, and let $v$ lie in $B := \mathrm{chartAlgFin}\,A\,K\,j$, the subalgebra of elements of $K$ integral over $A[j]$, with Laurent image either the modular unit $\Delta(q)\,\Delta(q^p)^{-1}$ or $p^{12}$ times its inverse. Then there exist a nonzero $\mathrm{avoid} \in \mathbb{F}_p[X]$, a nonzero $c_0 \in \mathbb{Z}[X]$ and $K_b \in \mathbb{N}$ such that for every monic $g \in \mathbb{Z}[X]$ of degree $\ge 1$ whose reduction mod $p$ is irreducible and coprime to $\mathrm{avoid}$, and with $g \nmid c_0$, the quotient $B/(g(v))$ is a finite free $A$-module, étale as an $A$-algebra, of rank between $1$ and $K_b \deg g$.
--
--   This is the construction of the level rings cut out on the affine chart of the two-chart integral model of $X_1(Mp)$ over $A$ by the values of the modular unit $\Delta(\tau)/\Delta(p\tau)$ (or its Atkin–Lehner conjugate $p^{12}/u$): all but finitely many residually irreducible monic polynomials $g$ produce finite étale $A$-algebras of rank controlled linearly in $\deg g$. It is used by [`ModularCurve.XOneP.exists_levelPolynomials_chartAlgFin_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_levelPolynomials_chartAlgFin_twoChartModel_x1_mul), which extracts from it a supply of level polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (v : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hv : ((v : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∨
      ((v : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹) :
    ∃ (avoid : Polynomial (ZMod p)) (_ : avoid ≠ 0) (c₀ : Polynomial ℤ) (_ : c₀ ≠ 0) (Kb : ℕ),
      ∀ g : Polynomial ℤ, g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod p))) →
        IsCoprime (g.map (Int.castRingHom (ZMod p))) avoid → ¬ g ∣ c₀ →
          Module.Finite A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Algebra.Etale A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.Free A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          1 ≤ Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ Kb * g.natDegree := by sorry
