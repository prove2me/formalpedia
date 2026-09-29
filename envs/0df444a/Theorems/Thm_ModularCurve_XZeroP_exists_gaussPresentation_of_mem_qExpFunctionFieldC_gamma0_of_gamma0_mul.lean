-- Prove2me | Theorems.Thm_ModularCurve_XZeroP_exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul
-- name    : ModularCurve.XZeroP.exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/fde00db2-be2f-5af9-97a2-275627b9c101
-- title:
--   Gauss-reduction lifting of the Γ₀(M) q-expansion field
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the $\mathbb{Q}$-subfield of $\mathbb{Q}((q))$ adjoining all quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$ attached to modular forms $f, g$ of a common weight $k$ on $\Gamma_0(Mp)$ with integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ in the sense of `IsIntegralQExp`, the denominator series being nonzero. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $\varpi$ a generator of the maximal ideal, $K$ an $A$-algebra compatibly with the tower, and let $j \in K$ be a nonzero element whose Laurent series is the coefficientwise image of $\mathrm{jq} = q^{-1}\cdot \mathrm{jNumQ}$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ admitting a Gauss presentation: there are $x, y \in A[[q]]$ with $\bar y \ne 0$ over the residue field $\kappa(A)$ and $f \cdot y = x$ in $L((q))$. The conclusion: every $z \in \kappa(A)((q))$ belonging to [`ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 M)`](def/ModularCurve_X1.html#L101) — the subfield of $\kappa(A)((q))$ generated over $\kappa(A)$ by the corresponding quotients of integral $q$-expansion series of modular forms on $\Gamma_0(M)$ — is the Gauss reduction of an element of $K$: there exist $f \in K$ and $x, y \in A[[q]]$ with $\bar y \ne 0$, $f \cdot y = x$ in $L((q))$, and $\bar x / \bar y = z$.
--
--   This is the surjectivity (lifting) half of the identification of the residue field of the Gauss valuation ring $W_0$ on the function field of $X_0(Mp)$ over $L$ with the level-$M$ $q$-expansion field over $\kappa(A)$, reflecting that the $\infty$-branch of the semistable reduction of $X_0(Mp)$ at $p$ is a copy of $X_0(M)$ with residue degree one. It is used in the description of inertia at supersingular points, entering the analysis of the $X_1(M)/X_0(p)$ integral model over $X_0(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XZeroP_exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XZeroP.exists_gaussPresentation_of_mem_qExpFunctionFieldC_gamma0_of_gamma0_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [NeZero p]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ z : LaurentSeries (IsLocalRing.ResidueField A),
      z ∈ ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 M) →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by sorry
