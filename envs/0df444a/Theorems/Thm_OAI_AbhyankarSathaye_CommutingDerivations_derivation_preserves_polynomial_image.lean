-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_derivation_preserves_polynomial_image
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:44:49.135483+00:00
-- url     : https://prove2.me/theorems/b374b82e-6597-440a-af0b-6c83b13e6851
-- title:
--   A derivation preserving the images of the variables preserves the image of the polynomial ring
-- statement:
--   Let $K$ be a commutative ring, $\sigma$ an arbitrary index set, $K[X_\sigma]$ the polynomial ring in the variables $X_j$, $j\in\sigma$, and $L$ a commutative $K$-algebra. Let $\iota:K[X_\sigma]\to L$ be a $K$-algebra homomorphism (not necessarily injective) and $D:L\to L$ a $K$-linear derivation. Suppose that for each $j\in\sigma$ there is a polynomial $q_j\in K[X_\sigma]$ with $\iota(q_j)=D(\iota(X_j))$. Then for every $p\in K[X_\sigma]$ there is $q\in K[X_\sigma]$ with $\iota(q)=D(\iota(p))$. In other words,
--
--   $$
--   D\bigl(\iota(X_j)\bigr)\in\iota\bigl(K[X_\sigma]\bigr)\ \text{ for all } j\in\sigma\quad\Longrightarrow\quad D\bigl(\iota(K[X_\sigma])\bigr)\subseteq\iota\bigl(K[X_\sigma]\bigr).
--   $$
--
--   The lemma reduces the question whether a derivation of a larger ring, such as a localization, maps the image of a polynomial ring into itself to a check on the variables alone. Neither finiteness of $\sigma$ nor any domain assumption is needed. It is the step that turns finitely many denominator bounds on the variables into a descended derivation of the whole polynomial ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/DenominatorDescent.lean#L18-L37

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

theorem OAI.AbhyankarSathaye.CommutingDerivations.derivation_preserves_polynomial_image [Algebra K L]
    (ι : MvPolynomial σ K →ₐ[K] L) (D : Derivation K L L)
    (hX : ∀ j : σ, ∃ q : MvPolynomial σ K, ι q = D (ι (X j))) :
    ∀ p : MvPolynomial σ K, ∃ q : MvPolynomial σ K, ι q = D (ι p) := by sorry
