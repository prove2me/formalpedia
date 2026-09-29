-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_gaussReduction_mem_x1FunctionFieldC_of_x1x0
-- name    : ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1FunctionFieldC_of_x1x0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/0dddedfe-aef9-5d2f-b331-4de4504081b0
-- title:
--   Gauss reduction of the Γ₁(M)∩Γ₀(p) q-expansion field at level M
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $M \ge 5$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K_1$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the coefficientwise image, under $\mathbb{Q} \to L$, of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 p)`. Let $A$ be a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$; $K_1$ is moreover an $A$-algebra compatibly with the tower $A \to L \to K_1$. Let $f \in K_1$ and $x, y \in A[[q]]$ be such that the reduction of $y$ modulo the maximal ideal is nonzero and, in $\mathrm{LaurentSeries}\,L$, $f \cdot y_L = x_L$, where $x_L, y_L$ denote the images of $x, y$ under coefficientwise application of $A \to L$ followed by the inclusion of power series into Laurent series. Then the quotient $\bar x / \bar y$ of the Laurent series attached to the reductions of $x$ and $y$ in the residue field $k$ of $A$ lies in [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134), the subfield of $k((q))$ generated over $k$ by `intFormRatiosC k (Gamma1 M)`.
--
--   This is the $q$-expansion form of the statement that the Gauss (coefficientwise) reduction of a $p$-integral function on the modular curve of level $\Gamma_1(M) \cap \Gamma_0(p)$ is a function of level $\Gamma_1(M)$ over the residue field: the Gauss valuation of $K_1$ corresponds to the $\infty$-component of the Deligne–Rapoport special fibre, which is identified with the level-$M$ curve in characteristic $p$ compatibly with $q$-expansions. It is used in the analysis of the valuation subrings and uniformisers of the $\Gamma_1(M) \cap \Gamma_0(p)$ function field above $p$, and in the corresponding discrete valuation ring and fraction field statements for the level-$M$ curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_gaussReduction_mem_x1FunctionFieldC_of_x1x0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1FunctionFieldC_of_x1x0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
        (f : ↥K₁) (x y : PowerSeries A) (hy : y.map (IsLocalRing.residue A) ≠ 0)
    (hxy : (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
      ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M := by sorry
