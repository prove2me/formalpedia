-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0
-- name    : ModularCurve.XOneGammaZeroP.smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/6bc337bb-b41e-58f7-9dec-5f588e2b9c29
-- title:
--   Group actions fixing K₂ preserve the Gauss valuation ring
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $M \neq 0$, $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Inside the Laurent series field $L((q))$ consider two intermediate fields over $L$: $K_1$, assumed equal to the base change [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) to $L$ of [`ModularCurve.x1x0FunctionFieldC ℚ M p`](def/ModularCurve_X1.html#L142), i.e. the subfield generated over $L$ by the coefficientwise images of the field generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions of modular forms of equal weight for $\Gamma_1(M) \cap \Gamma_0(p)$ (with $\mathrm{intSeriesC}(p_g) \neq 0$); and $K_2$, assumed equal to the corresponding base change of the analogous $q$-expansion field for $\Gamma_0(Mp)$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$ in $L$, together with an $A$-algebra structure on $K_1$ compatible with that on $L$. Let $W_0$ be a valuation subring of $K_1$ whose members are exactly those $f$ for which there are power series $x, y$ over $A$ with the reduction of $y$ modulo the maximal ideal of $A$ nonzero and $f \cdot y = x$ in $L((q))$, the coefficients of $x$ and $y$ being mapped into $L$ (the Gauss valuation ring). Finally let $G$ be a finite group acting on $K_1$ by ring automorphisms, such that every $g \in G$ fixes each element of $K_1$ whose underlying Laurent series lies in $K_2$. Then for every $g \in G$ and every $f \in W_0$ one has $g \cdot f \in W_0$; that is, $W_0$ is stable under the action of $G$.
--
--   The group $G$ plays the role of the diamond automorphisms of the function field of $X(\Gamma_1(M) \cap \Gamma_0(p))$ over that of $X_0(Mp)$, and the assertion is that each of them carries the Gauss valuation ring to itself — so that the diamonds preserve the corresponding sheet of the special fibre rather than interchanging sheets. It is used in the computation of the inertia and of the automorphisms acting trivially on the residue field at that place, in particular by [`ModularCurve.XOneGammaZeroP.eq_one_of_forall_smul_sub_mem_nonunits_gauss_x1x0_gamma0`](thm.html#ModularCurve.XOneGammaZeroP.eq_one_of_forall_smul_sub_mem_nonunits_gauss_x1x0_gamma0) and by the bounds on the inertia group at points of the two-chart integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneGammaZeroP.smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (G : Type) [Group G] [Fintype G] [MulSemiringAction G ↥K₁]
    (hGfixK : ∀ (g : G) (x : ↥K₁), (x : LaurentSeries L) ∈ K₂ → g • x = x) :
    ∀ (g : G) (f : ↥K₁), f ∈ W₀ → g • f ∈ W₀ := by sorry
