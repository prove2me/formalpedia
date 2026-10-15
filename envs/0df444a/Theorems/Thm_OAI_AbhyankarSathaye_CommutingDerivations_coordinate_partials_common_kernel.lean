-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_coordinate_partials_common_kernel
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:49:11.904479+00:00
-- url     : https://prove2.me/theorems/5f81da55-9cd6-4739-823f-d2a091d8a2a2
-- title:
--   In characteristic zero, the common kernel of the coordinate partial derivatives is the coefficient ring
-- statement:
--   Let $B$ be an integral domain of characteristic zero, $\sigma$ an arbitrary index set, and $p\in B[X_\sigma]$ a polynomial in the variables $X_i$, $i\in\sigma$. Then $p$ is annihilated by every coordinate partial derivative if and only if it is constant:
--
--   $$
--   \frac{\partial p}{\partial X_i}=0\ \text{ for all } i\in\sigma\quad\Longleftrightarrow\quad p=b\ \text{ for some } b\in B,
--   $$
--
--   where $b$ is regarded as a constant polynomial. Hence the common kernel of the derivations $\partial/\partial X_i$, $i\in\sigma$, is exactly the coefficient ring $B$.
--
--   In the construction of the commuting family this is applied with $B=\mathbb{C}[t,t^{-1}]$, the ring of Laurent polynomials, which is an integral domain of characteristic zero, and with $\sigma=\{0,\dots,n-2\}$: the common kernel of the partial derivatives in Laurent coordinates is the Laurent coefficient ring, which the kernel intersection theorem then identifies, inside $\mathbb{C}[X_0,\dots,X_{n-1}]$, with $\mathbb{C}[F_n]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/CoordinatePartials.lean#L89-L105

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

theorem OAI.AbhyankarSathaye.CommutingDerivations.coordinate_partials_common_kernel [IsDomain B] [CharZero B]
    (p : MvPolynomial σ B) :
    (∀ i, pderiv i p = 0) ↔ ∃ b : B, p = C b := by sorry
