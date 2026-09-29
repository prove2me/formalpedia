-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation
-- name    : ModularCurve.exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/7425d3fd-ff41-5ea4-91a0-78757e5d1d27
-- title:
--   Non-units of the Gauss valuation ring are divisible by varpi
-- statement:
--   Let $L$ be a field of characteristic zero and let $K$ be an intermediate field of the extension $L \subseteq L((q))$, where $L((q))$ denotes the field of formal Laurent series (Hahn series over $\mathbb{Z}$) in one variable over $L$. Let $A$ be a commutative domain which is a discrete valuation ring, equipped with an $L$-algebra structure making $L$ its fraction field, and with an $A$-algebra structure on $K$ compatible with that of $L$ via the scalar tower $A \to L \to K$. Let $\varpi \in A$ generate the maximal ideal of $A$. Let $W_0$ be a valuation subring of $K$ whose underlying set is assumed to be described by a Gauss presentation: an element $f \in K$ lies in $W_0$ if and only if there are power series $x, y \in A[[T]]$ such that the reduction of $y$ modulo the maximal ideal of $A$ (coefficientwise, via the residue map) is nonzero and, in $L((q))$, the image of $f$ times the Laurent series attached to $y$ (coefficients pushed into $L$) equals the Laurent series attached to $x$. The conclusion is that every non-unit $f$ of $W_0$, in the sense of Mathlib's `ValuationSubring.nonunits` (equivalently, $W_0$-valuation strictly less than $1$), can be written as $f = \varpi \cdot g$ with $g \in W_0$, where $\varpi$ is viewed in $K$ through the structure map $A \to K$.
--
--   This is the statement that on the Gauss branch the extension of $A$ to the valuation ring $W_0$ has ramification index one: a uniformiser of $A$ is a uniformiser of $W_0$, so that the maximal ideal of $W_0$ is $\varpi W_0$. It is used in the analysis of the modular curve of full level, in particular in the verifications that certain points of the $j$-line or the $q$-expansion charts are unramified and in the construction of elements with prescribed integrality on the Gauss branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ f : ↥K, f ∈ W₀.nonunits → ∃ g : ↥K, g ∈ W₀ ∧ f = algebraMap A ↥K ϖ * g := by sorry
