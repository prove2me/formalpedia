-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_exists_common_denominator_descent
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:45:51.462297+00:00
-- url     : https://prove2.me/theorems/0df1d739-2142-4bdb-9c1d-69a014b03b9f
-- title:
--   Finitely many derivations of $K[X_\sigma][c^{-1}]$ descend to $K[X_\sigma]$ after multiplication by a common power of $c$
-- statement:
--   Let $K$ be a commutative ring, $\sigma$ and $\tau$ finite index sets, and $c\in K[X_\sigma]$. Let $L$ be a commutative ring that is both a $K$-algebra and a $K[X_\sigma]$-algebra, compatibly (the action of $K$ on $L$ factors through $K[X_\sigma]$), and that is a localization of $K[X_\sigma]$ away from $c$, with structure map $\lambda:K[X_\sigma]\to L$. Assume that $\lambda$ is injective. Then for every family $(D_i)_{i\in\tau}$ of $K$-linear derivations of $L$ there exist an exponent $N\in\mathbb{N}$ and $K$-linear derivations $d_i$ ($i\in\tau$) of $K[X_\sigma]$ such that
--
--   $$
--   \lambda\bigl(d_i(p)\bigr)=\lambda(c)^N\,D_i\bigl(\lambda(p)\bigr)\qquad\text{for all } i\in\tau \text{ and } p\in K[X_\sigma].
--   $$
--
--   Thus, after multiplication by one common power of $c$, finitely many derivations of the localization $K[X_\sigma][c^{-1}]$ restrict to derivations of the polynomial ring itself. This is how derivations of $\mathbb{C}[X_0,\dots,X_{n-1}]$ are obtained from the coordinate partial derivatives of its localization at $F_n+1$.
--
--   **Formalization Note** The compatibility of the two algebra structures is the instance `[IsScalarTower K (MvPolynomial σ K) L]`, and the localization is `[IsLocalization.Away c L]`. Injectivity of the structure map is an explicit hypothesis; it holds, for instance, when $K[X_\sigma]$ is a domain and $c\ne0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/DenominatorDescent.lean#L70-L94

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
variable {K σ τ L : Type*} [CommRing K] [CommRing L]
variable [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ K) L]
variable [Algebra K L] [IsScalarTower K (MvPolynomial σ K) L]

theorem OAI.AbhyankarSathaye.CommutingDerivations.exists_common_denominator_descent (c : MvPolynomial σ K)
    [IsLocalization.Away c L]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ K) L))
    (D : τ → Derivation K L L) :
    ∃ (N : ℕ) (d : τ → Derivation K (MvPolynomial σ K) (MvPolynomial σ K)),
      ∀ (i : τ) (p : MvPolynomial σ K),
        algebraMap (MvPolynomial σ K) L (d i p) =
          (algebraMap (MvPolynomial σ K) L c)^N *
            D i (algebraMap (MvPolynomial σ K) L p) := by sorry
