-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
-- name    : ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/46e673c5-0be5-531d-8565-3dc5c99c28d2
-- title:
--   Level-p automorphism with σ(j)=j(qᵖ) moving the Gauss ring
-- statement:
--   Let $p$ be prime and $M\ge 5$ with $p\nmid M$, let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta\in L$ be a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L\subseteq L((q))$ obtained by adjoining to $L$ the coefficientwise image, under the map $\mathbb{Q}((q))\to L((q))$ induced by $\mathbb{Q}\to L$, of the $q$-expansion function field $\mathtt{x1FunctionFieldC}\ \mathbb{Q}\ (\Gamma_1(Mp))$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, with $A$ acting on $K$ compatibly through $L$. Let $j\in K$ be nonzero and have Laurent image $q^{-1}$ times the power series $\mathtt{jNumQ}$, i.e. the $q$-expansion of the modular invariant. Then there is an $L$-algebra automorphism $\sigma$ of $K$ with: (i) the Laurent image of $\sigma(j)$ is the $q\mapsto q^p$ substitution of that of $j$; (ii) $\sigma$ preserves the integral closure of $A[j]$ in $K$, in both directions; and (iii) for every valuation subring $W_0$ of $K$ whose members are exactly the $f$ admitting a presentation $f\,y=x$ in $L((q))$ with $x,y$ power series over $A$ and the reduction of $y$ modulo the maximal ideal nonzero, the subring $\{b:\sigma(b)\in W_0\}$ differs from $W_0$, and for every polynomial $P$ over $A$ with nonzero reduction both $P(j)$ and $P(j)^{-1}$ lie in $\{b:\sigma(b)\in W_0\}$.
--
--   This records the level-$p$ involution $w_\zeta$ of the modular curve of level $\Gamma_1(Mp)$ in the $q$-expansion model: on the Tate curve it sends $\mathrm{Tate}(q)$ to $\mathrm{Tate}(q^p)$, so that $j\mapsto j(q^p)$, it respects the integral $j$-chart over $A$, and it carries the Gauss valuation ring of $A$-integral $q$-expansions to a different valuation ring lying over the generic point of the $j$-line in the special fibre. It feeds the analysis of the two-chart integral model of the curve, in particular the identification of pairs of valuation subrings and the comparison of stalks at the points of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,

      ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∧

      (∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
        σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ∧

      (∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
          (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)) := by sorry
