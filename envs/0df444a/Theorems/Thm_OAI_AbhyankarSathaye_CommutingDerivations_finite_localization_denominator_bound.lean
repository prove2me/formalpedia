-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_finite_localization_denominator_bound
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:45:34.03778+00:00
-- url     : https://prove2.me/theorems/ce0dea93-d7e0-4bda-a559-2bb9c8b700e5
-- title:
--   A single power of $c$ clears the denominators of finitely many elements of a localization
-- statement:
--   Let $K$ be a commutative ring, $\sigma$ and $\tau$ finite index sets, $c\in K[X_\sigma]$ a polynomial, and $L$ a commutative ring that is a localization of $K[X_\sigma]$ away from $c$, with structure map $\lambda:K[X_\sigma]\to L$. Then for every finite family $(z_{ij})_{i\in\tau,\,j\in\sigma}$ of elements of $L$ there is a single exponent $N\in\mathbb{N}$ that clears all denominators at once: for all $i\in\tau$ and $j\in\sigma$ there is $a_{ij}\in K[X_\sigma]$ with
--
--   $$
--   \lambda(a_{ij})=\lambda(c)^N\,z_{ij}.
--   $$
--
--   Each element of $L=K[X_\sigma][c^{-1}]$ is a fraction whose denominator is a power of $c$; the point is that finitely many elements share a common power. In the construction of the commuting derivations it is applied to $z_{ij}=D_i(\lambda(X_j))$, the images of the variables under finitely many derivations $D_i$ of the localization. No domain hypothesis is needed, and $c$ may be a zero divisor.
--
--   **Formalization Note** The family is a function `z : τ → σ → L`, with `[Fintype σ] [Fintype τ]`. Although the localized ring is `MvPolynomial σ K`, only the localization property of $L$ is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/DenominatorDescent.lean#L43-L66

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

theorem OAI.AbhyankarSathaye.CommutingDerivations.finite_localization_denominator_bound (c : MvPolynomial σ K)
    [IsLocalization.Away c L] (z : τ → σ → L) :
    ∃ N : ℕ, ∀ (i : τ) (j : σ), ∃ a : MvPolynomial σ K,
      algebraMap (MvPolynomial σ K) L a =
        (algebraMap (MvPolynomial σ K) L c)^N * z i j := by sorry
