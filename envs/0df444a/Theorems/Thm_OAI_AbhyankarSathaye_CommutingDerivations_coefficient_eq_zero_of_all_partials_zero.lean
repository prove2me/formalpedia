-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_coefficient_eq_zero_of_all_partials_zero
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:48:50.548104+00:00
-- url     : https://prove2.me/theorems/7cc8f3b8-dd2d-4fd6-ac7e-0d489fbf6b2e
-- title:
--   In characteristic zero, a polynomial killed by all partial derivatives has no nonconstant terms
-- statement:
--   Let $B$ be an integral domain of characteristic zero, $\sigma$ an arbitrary index set, and $p\in B[X_\sigma]$ a polynomial all of whose partial derivatives vanish: $\partial p/\partial X_i=0$ for every $i\in\sigma$. For a finitely supported exponent vector $m:\sigma\to\mathbb{N}$ let $[X^m]\,p$ denote the coefficient of the monomial $X^m=\prod_k X_k^{m_k}$ in $p$. Then every coefficient of $p$ at a nonzero exponent vanishes:
--
--   $$
--   [X^m]\,p=0\qquad\text{for every exponent vector } m\ne0 .
--   $$
--
--   This is the coefficientwise half of the statement that, in characteristic zero, the common kernel of all coordinate partial derivatives is the coefficient ring. The characteristic hypothesis cannot be dropped: in characteristic $2$ the polynomial $X^2$ has zero derivative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/CoordinatePartials.lean#L67-L87

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations

open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial
variable {B σ : Type*} [CommRing B]

theorem OAI.AbhyankarSathaye.CommutingDerivations.coefficient_eq_zero_of_all_partials_zero [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) (hp : ∀ i, pderiv i p = 0)
    (m : σ →₀ ℕ) (hm : m ≠ 0) : p.coeff m = 0 := by sorry
