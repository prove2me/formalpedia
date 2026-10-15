-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_coordinate_partial_iterate_eq_zero
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:48:31.183911+00:00
-- url     : https://prove2.me/theorems/689e74ef-5690-49c6-990c-709c2fb72d1f
-- title:
--   The $n$-th iterate of $\partial/\partial X_i$ kills every polynomial of degree less than $n$ in $X_i$
-- statement:
--   Let $B$ be a commutative ring, $\sigma$ an arbitrary index set, and $B[X_\sigma]$ the polynomial ring in the variables $X_k$, $k\in\sigma$. For a finitely supported exponent vector $m:\sigma\to\mathbb{N}$ write $[X^m]\,p$ for the coefficient of the monomial $X^m=\prod_k X_k^{m_k}$ in $p$, and write $\partial_i=\partial/\partial X_i$. Fix $i\in\sigma$, $n\in\mathbb{N}$ and $p\in B[X_\sigma]$, and suppose that $p$ has no monomial of degree at least $n$ in $X_i$, that is, $[X^m]\,p=0$ whenever $m_i\ge n$. Then the $n$-fold iterate of $\partial_i$ annihilates $p$:
--
--   $$
--   \partial_i^{\,n}\,p=\underbrace{\partial_i\circ\cdots\circ\partial_i}_{n\text{ times}}(p)=0.
--   $$
--
--   Since every polynomial has finite degree in $X_i$, this shows that $\partial/\partial X_i$ is locally nilpotent on $B[X_\sigma]$; this is the local nilpotency of the ordinary coordinate partials that appear in the commuting family. The statement holds over every commutative ring, with no assumption on the characteristic. For $n=0$ the hypothesis forces $p=0$, and the conclusion is the trivial identity $p=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/CoordinatePartials.lean#L27-L46

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

theorem OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partial_iterate_eq_zero (i : σ) (n : ℕ) (p : MvPolynomial σ B)
    (hp : ∀ m : σ →₀ ℕ, n ≤ m i → p.coeff m = 0) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[n] p = 0 := by sorry
